package tip.analysis

import tip.ast._
import tip.ast.AstNodeData.DeclarationData
import tip.cfg._
import tip.lattices.{FlatLattice, MapLattice}
import tip.util.MessageHandler

/**
  * The ownership four status of a variable.
  */
object OwnershipStatus extends Enumeration {
  val HeapOwner, HeapNotOwner, Pointer, Other = Value
}

/**
  * The flat lattice of ownership statuses: Bot < {HeapOwner, HeapNotOwner, Pointer, Other} < Top.
  */
object OwnershipLattice extends FlatLattice[OwnershipStatus.Value]

/**
  * Used SimpleSignAnalysis.scala as a template
  *   
  * Forward and intraprocedural ownership analysis.
  *
  * Track a unique owner for each heap-allocated memory location
  * Reports all ownership errors and warnings through a [[MessageHandler]].
  */
class OwnershipAnalysis(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData) extends FlowSensitiveAnalysis(true) {

  import OwnershipStatus._

  /**
    * The lattice of abstract values.
    */
  val valuelattice: OwnershipLattice.type = OwnershipLattice

  import valuelattice.{Bot, FlatEl, Top}

  /**
    * The lattice of abstract states.
    */
  val statelattice: MapLattice[ADeclaration, valuelattice.type] = new MapLattice(valuelattice)

  /**
    * The program lattice.
    */
  val lattice: MapLattice[CfgNode, statelattice.type] = new MapLattice(statelattice)

  /**
    * The domain of the program lattice.
    */
  val domain: Set[CfgNode] = cfg.nodes

  /**
    * Records the latest error or warning for each program location.
    */
  val msgs = new MessageHandler

  NoRecords.assertContainsProgram(cfg.prog)

  /**
    * Preparing for Section 5
    * The initial ownership status of a function parameter.
    * The parameters of <main> are always integers.
    * Other parameters are unknown in this untyped analysis, so they start at Top.
    * TypedOwnershipAnalysis can override this to use the inferred types.
    */
  protected def initialParamStatus(fun: AFunDeclaration, param: AIdentifierDeclaration): valuelattice.Element =
    if (fun.name == "main") FlatEl(Other) else Top

    /**
    * Abstract evaluation of expressions, including the ownership checks on `&x` and `*x`.
    */
  def eval(exp: AExpr, env: statelattice.Element): valuelattice.Element =
    exp match {
      case id: AIdentifier => env(declData(id)) // Rule: variable status is the state
      case _: ANumber | _: AInput => FlatEl(Other) // Rule: all integer values and constants evaluate to Other
      case bin: ABinaryOp =>
        eval(bin.left, env)
        eval(bin.right, env)
        FlatEl(Other) // Rule: Binary operators produce integers. Check both sides.
      case alloc: AAlloc =>
        eval(alloc.exp, env)
        FlatEl(HeapOwner) // Rule: Alloc evaluates to HeapOwner
      case ref: AVarRef => // &x
        // Rule: only stack (non-heap) variables may have their address taken
        if (env(declData(ref.id)) == FlatEl(Other))
          msgs.message(msgs.Reason.None, ref.loc)
        else
          msgs.message(msgs.Reason.OwnershipError, ref.loc, s"cannot take address of non-stack variable: ${ref.id}")
        FlatEl(Pointer)
      case AUnaryOp(DerefOp, sub, loc) => // *x
        // Rule: overloaded dereference: allowed through a pointer or by the owner of a heap cell
        eval(sub, env) match {
          case FlatEl(Pointer) | FlatEl(HeapOwner) =>
            msgs.message(msgs.Reason.None, loc)
          case Top =>
            msgs.message(msgs.Reason.OwnershipWarning, loc, s"dereference when may not be owner: $sub")
          case _ =>
            msgs.message(msgs.Reason.OwnershipError, loc, s"illegal dereference when not owner: $sub")
        }
        FlatEl(Other) // all heap cells and pointers contain integers
      case _: ANull => FlatEl(Pointer) // NOTE: null is not a HEAP cell with an owner. It should be a non-heap Pointer
      case call: ACallFuncExpr =>
        // Rule: intraprocedural - the result of a call is unknown (TOP)
        call.args.foreach(eval(_, env))
        Top
      case _ => Top // NOTE: Records are not included, so TOP is the safest status
    }

  /**
    * Transfer functions for the different kinds of CFG nodes.
    */
  def localTransfer(n: CfgNode, s: statelattice.Element): statelattice.Element =
    n match {
      case entry: CfgFunEntryNode =>
        s ++ entry.data.params.map(p => p -> initialParamStatus(entry.data, p))
      case r: CfgStmtNode =>
        r.data match {
          // var declarations
          case varr: AVarStmt => s ++ varr.declIds.map(_ -> valuelattice.bottom)

          // x = y : ownership moves from y to x
          case AAssignStmt(x: AIdentifier, y: AIdentifier, _) =>
            val xd = declData(x)
            val yd = declData(y)
            val o = eval(y, s)
            if (xd == yd) s // self-assignment moves nothing
            else s + (xd -> o) + (yd -> (if (o == FlatEl(HeapOwner)) FlatEl(HeapNotOwner) else o))

          // Rule: x = E, where E is not an identifier
          case AAssignStmt(x: AIdentifier, e, _) => s + (declData(x) -> eval(e, s))

          // Rule: *x = E : only an owner or a pointer may store into the cell
          case AAssignStmt(dw: ADerefWrite, e, _) =>
            eval(e, s)
            eval(dw.exp, s) match {
              case FlatEl(Pointer) | FlatEl(HeapOwner) =>
                msgs.message(msgs.Reason.None, dw.loc)
              case _ =>
                msgs.message(msgs.Reason.OwnershipError, dw.loc, s"illegal store when not owner or pointer: ${dw.exp}")
            }
            s // State does not change. No change in ownership status. Only change in heap cell's content

          // conditions, output, return: no state change, but check the expression. JOIN(v), with check on eval(E)
          case cond: AExpr => eval(cond, s); s
          case out: AOutputStmt => eval(out.exp, s); s
          case ret: AReturnStmt => eval(ret.exp, s); s
          case err: AErrorStmt => eval(err.exp, s); s

          case _ => s
        }
      case _ => s
    }

  /**
    * The constraint function for individual elements in the map domain.
    */
  def funsub(n: CfgNode, x: lattice.Element): lattice.sublattice.Element =
    localTransfer(n, join(n, x))

  /**
    * Computes the least upper bound of the states of the predecessors.
    */
  def join(n: CfgNode, o: lattice.Element): lattice.sublattice.Element = {
    val states = n.pred.map(o(_))
    states.foldLeft(lattice.sublattice.bottom)((acc, pred) => lattice.sublattice.lub(acc, pred))
  }

  /**
    * The function for which the least fixpoint is computed.
    */
  def fun(x: lattice.Element): lattice.Element =
    domain.foldLeft(lattice.bottom)((m, a) => m + (a -> funsub(a, x)))

  /**
    * The basic Kleene fixpoint solver, followed by printing the ownership messages.
    * printMessages throws an exception if any ownership error was found.
    */
  def analyze(): lattice.Element = {
    var x = lattice.bottom
    var t = x
    do {
      t = x
      x = fun(x)
    } while (x != t)
    msgs.printMessages() // Printing after the fixpoint. Only final results are printed.
    x
  }
}
