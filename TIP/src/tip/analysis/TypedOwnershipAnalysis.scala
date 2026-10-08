package tip.analysis

import tip.ast._
import tip.ast.AstNodeData.{AstNodeWithType, DeclarationData, TypeData}
import tip.cfg.IntraproceduralProgramCfg
import tip.types._

/**
  * Typed ownership analysis.
  *
  * Same rules as [[OwnershipAnalysis]], BUT function parameters start with the
  * ownership status implied by their inferred type, instead of Top.
  * Type inference is run automatically when the analysis is created.
  */
class TypedOwnershipAnalysis(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData) extends OwnershipAnalysis(cfg) {

  import OwnershipStatus._
  import valuelattice.{FlatEl, Top}

  /**
    * The inferred type of every declaration and expression in the program.
    * (Throws a TipProgramException if the program is not type correct.)
    */
  implicit val typeData: TypeData = new TypeAnalysis(cfg.prog).analyze()

  /**
    * The ownership status implied by a type.
    */
  private def statusOfType(t: Type): valuelattice.Element =
    t match {
      case RefType(HeapKind, _) => FlatEl(HeapOwner) // Heap-allocated type
      case RefType(BorrowKind, _) => FlatEl(Pointer) // Pointer type
      case RefType(_, _) => Top // a reference whose kind (heap or pointer) is unknown
      case RecursiveType(_, body: Type) => statusOfType(body)
      case _: FreshVarType | _: VarType => Top // unconstrained type: could be anything
      case _ => FlatEl(Other) // int and function types are non-heap
    }

  /**
    * Parameters start with the status implied by their inferred type.
    */
  override protected def initialParamStatus(fun: AFunDeclaration, param: AIdentifierDeclaration): valuelattice.Element =
    param.theType.map(statusOfType).getOrElse(Top)
}


