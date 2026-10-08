package tip.analysis
// Use OwnershipAnalysis.scala as Template
import tip.ast._
import tip.ast.AstNodeData.DeclarationData
import tip.cfg._
import tip.lattices.{LiftLattice, MapLattice}
import tip.solvers.{MapLiftLatticeSolver, WorklistFixpointSolverWithReachability}

/**
  * Interprocedural (context-insensitive) ownership analysis,
  * using the worklist solver with reachability (`-ownership iwlr`). Like SigAnalysis
  *
  * Uses the same ownership rules as [[OwnershipAnalysis]], plus:
  *  - a function's parameters receive the statuses of the arguments at all its call sites;
  *  - heap owners passed as arguments move their ownership into the callee;
  *  - the status of the returned value flows back to the variable assigned at the call site.
  *
  * Requires the program to be normalized with -normalizecalls and -normalizereturns.
  */
class InterprocOwnershipAnalysis(val cfg: InterproceduralProgramCfg)(implicit val declData: DeclarationData)
    extends FlowSensitiveAnalysis(true)
    with OwnershipFunctions
    with MapLiftLatticeSolver[CfgNode]
    with WorklistFixpointSolverWithReachability[CfgNode]
    with InterproceduralForwardDependencies {

  import cfg._
  import OwnershipStatus._
  import valuelattice.FlatEl

  /**
    * Lifted state lattice, whose extra bottom element represents "unreachable".
    */
  val liftedstatelattice: LiftLattice[statelattice.type] = new LiftLattice(statelattice)

  /**
    * The program lattice.
    */
  val lattice: MapLattice[CfgNode, liftedstatelattice.type] = new MapLattice(liftedstatelattice)

  val domain: Set[CfgNode] = cfg.nodes

  /**
    * The analysis starts at the entry of main.
    */
  val first: Set[CfgNode] = Set(cfg.funEntries(cfg.program.mainFunction))

  NoRecords.assertContainsProgram(cfg.program)

  /**
    * Transfer function for reachable nodes inside a function.
    */
  def transferUnlifted(n: CfgNode, s: statelattice.Element): statelattice.Element =
    n match {
      // return E : remember the status of the returned value in the special #result variable
      case CfgStmtNode(_, _, _, ret: AReturnStmt) =>
        s + (AstOps.returnId -> eval(ret.exp, s))
      // call and exit nodes: no-ops (the work is done at function entries and after-calls)
      case _: CfgCallNode | _: CfgFunExitNode => s
      case _ => localTransfer(n, s)
    }

  /**
    * Adds the interprocedural flow at function entries and after-call nodes.
    */
  override def funsub(n: CfgNode, x: lattice.Element): liftedstatelattice.Element = {
    import liftedstatelattice._

    new NormalizedCalls().assertContainsNode(n.data)

    n match {
      // function entry: parameters get the join of the argument statuses at all reachable call sites
      case entry: CfgFunEntryNode =>
        val fromCallers = entry.callers.foldLeft(bottom) { (acc, call) =>
          x(call) match {
            case Lift(callState) =>
              val paramState = entry.data.params.zip(call.invocation.args).foldLeft(statelattice.bottom) {
                case (st, (param, arg)) => st + (param -> eval(arg, callState))
              }
              lub(acc, Lift(paramState))
            case Bottom => acc // this call site is not reachable (yet)
          }
        }
        if (entry.data.name == "main")
          // main is always reachable, and its parameters are integers
          lub(fromCallers, Lift(localTransfer(entry, statelattice.bottom)))
        else fromCallers

      // after-call: caller's state before the call, with owner arguments moved and the result assigned
      case aftercall: CfgAfterCallNode =>
        val returned = aftercall.calledExit.foldLeft(bottom) { (acc, exit) => lub(acc, x(exit)) }
        (x(aftercall.callNode), returned) match {
          case (Lift(callState), Lift(exitState)) =>
            // heap owners passed as arguments have moved their ownership into the callee
            val moved = aftercall.invocation.args.foldLeft(callState) {
              case (st, id: AIdentifier) if st(declData(id)) == FlatEl(HeapOwner) =>
                st + (declData(id) -> FlatEl(HeapNotOwner))
              case (st, _) => st
            }
            Lift(moved + (declData(aftercall.targetIdentifier) -> exitState(AstOps.returnId)))
          case _ => Bottom // the call is not reachable, or the callee has not returned (yet)
        }

      case _ => super.funsub(n, x)
    }
  }

  /**
    * Runs the worklist solver, then prints the ownership messages.
    * printMessages throws an exception if any ownership error was found.
    */
  override def analyze(): lattice.Element = {
    val result = super.analyze()
    msgs.printMessages()
    result
  }
}
