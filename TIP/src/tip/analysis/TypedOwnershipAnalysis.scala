package tip.analysis

import tip.ast._
import tip.ast.AstNodeData.{AstNodeWithType, DeclarationData, TypeData}
import tip.cfg.IntraproceduralProgramCfg
import tip.types._

/**
  * Typed ownership analysis.
  *
  * Same rules as [[OwnershipAnalysis]], but function parameters start with the
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

  
}


