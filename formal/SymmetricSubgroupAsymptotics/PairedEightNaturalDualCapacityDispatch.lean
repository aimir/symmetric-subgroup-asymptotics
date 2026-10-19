import SymmetricSubgroupAsymptotics.PairedEightSixTopAnchorEnvelopes
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow2NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow3NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow4NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow5NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow6NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow7NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow8NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow9NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow10NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow11NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow12NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow13NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow14NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow15NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow16NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow17NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow18NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow19NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow20NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow21NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow22NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow23NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow24NaturalModule

/-! Exact natural-module dispatch: six two-generator rows and eighteen
one-generator rows. All bounds come from the original checked modules. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops

def naturalCapacity : Fin 24 → ℕ :=
  ![2,2,1,1,1,2,1,1,1,1,2,2,1,1,2,1,1,1,1,1,1,1,1,1]

set_option maxHeartbeats 1000000 in
theorem natural_dual_uniform (j : Fin 24) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) (interface j).top (Fin 8)).dual
      (naturalCapacity j) := by
  fin_cases j
  · change UniformSubrepresentationGeneratorBound
      PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.representation.dual 2
    exact PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.dualUniform
  · change UniformSubrepresentationGeneratorBound
      PrimitiveAffineDegreeTwoPairedEightRow2NaturalModule.representation.dual 2
    exact PrimitiveAffineDegreeTwoPairedEightRow2NaturalModule.dualUniform
  · change UniformSubrepresentationGeneratorBound
      PrimitiveAffineDegreeTwoPairedEightRow3NaturalModule.representation.dual 1
    exact PrimitiveAffineDegreeTwoPairedEightRow3NaturalModule.dualUniform
  · change UniformSubrepresentationGeneratorBound
      PrimitiveAffineDegreeTwoPairedEightRow4NaturalModule.representation.dual 1
    exact PrimitiveAffineDegreeTwoPairedEightRow4NaturalModule.dualUniform
  · change UniformSubrepresentationGeneratorBound
      PrimitiveAffineDegreeTwoPairedEightRow5NaturalModule.representation.dual 1
    exact PrimitiveAffineDegreeTwoPairedEightRow5NaturalModule.dualUniform
  · change UniformSubrepresentationGeneratorBound
      PrimitiveAffineDegreeTwoPairedEightRow6NaturalModule.representation.dual 2
    exact PrimitiveAffineDegreeTwoPairedEightRow6NaturalModule.dualUniform
  · change UniformSubrepresentationGeneratorBound
      PrimitiveAffineDegreeTwoPairedEightRow7NaturalModule.representation.dual 1
    exact PrimitiveAffineDegreeTwoPairedEightRow7NaturalModule.dualUniform
  · change UniformSubrepresentationGeneratorBound
      PrimitiveAffineDegreeTwoPairedEightRow8NaturalModule.representation.dual 1
    exact PrimitiveAffineDegreeTwoPairedEightRow8NaturalModule.dualUniform
  · change UniformSubrepresentationGeneratorBound
      PrimitiveAffineDegreeTwoPairedEightRow9NaturalModule.representation.dual 1
    exact PrimitiveAffineDegreeTwoPairedEightRow9NaturalModule.dualUniform
  · change UniformSubrepresentationGeneratorBound
      PrimitiveAffineDegreeTwoPairedEightRow10NaturalModule.representation.dual 1
    exact PrimitiveAffineDegreeTwoPairedEightRow10NaturalModule.dualUniform
  · change UniformSubrepresentationGeneratorBound
      PrimitiveAffineDegreeTwoPairedEightRow11NaturalModule.representation.dual 2
    exact PrimitiveAffineDegreeTwoPairedEightRow11NaturalModule.dualUniform
  · change UniformSubrepresentationGeneratorBound
      PrimitiveAffineDegreeTwoPairedEightRow12NaturalModule.representation.dual 2
    exact PrimitiveAffineDegreeTwoPairedEightRow12NaturalModule.dualUniform
  · change UniformSubrepresentationGeneratorBound
      PrimitiveAffineDegreeTwoPairedEightRow13NaturalModule.representation.dual 1
    exact PrimitiveAffineDegreeTwoPairedEightRow13NaturalModule.dualUniform
  · change UniformSubrepresentationGeneratorBound
      PrimitiveAffineDegreeTwoPairedEightRow14NaturalModule.representation.dual 1
    exact PrimitiveAffineDegreeTwoPairedEightRow14NaturalModule.dualUniform
  · change UniformSubrepresentationGeneratorBound
      PrimitiveAffineDegreeTwoPairedEightRow15NaturalModule.representation.dual 2
    exact PrimitiveAffineDegreeTwoPairedEightRow15NaturalModule.dualUniform
  · change UniformSubrepresentationGeneratorBound
      PrimitiveAffineDegreeTwoPairedEightRow16NaturalModule.representation.dual 1
    exact PrimitiveAffineDegreeTwoPairedEightRow16NaturalModule.dualUniform
  · change UniformSubrepresentationGeneratorBound
      PrimitiveAffineDegreeTwoPairedEightRow17NaturalModule.representation.dual 1
    exact PrimitiveAffineDegreeTwoPairedEightRow17NaturalModule.dualUniform
  · change UniformSubrepresentationGeneratorBound
      PrimitiveAffineDegreeTwoPairedEightRow18NaturalModule.representation.dual 1
    exact PrimitiveAffineDegreeTwoPairedEightRow18NaturalModule.dualUniform
  · change UniformSubrepresentationGeneratorBound
      PrimitiveAffineDegreeTwoPairedEightRow19NaturalModule.representation.dual 1
    exact PrimitiveAffineDegreeTwoPairedEightRow19NaturalModule.dualUniform
  · change UniformSubrepresentationGeneratorBound
      PrimitiveAffineDegreeTwoPairedEightRow20NaturalModule.representation.dual 1
    exact PrimitiveAffineDegreeTwoPairedEightRow20NaturalModule.dualUniform
  · change UniformSubrepresentationGeneratorBound
      PrimitiveAffineDegreeTwoPairedEightRow21NaturalModule.representation.dual 1
    exact PrimitiveAffineDegreeTwoPairedEightRow21NaturalModule.dualUniform
  · change UniformSubrepresentationGeneratorBound
      PrimitiveAffineDegreeTwoPairedEightRow22NaturalModule.representation.dual 1
    exact PrimitiveAffineDegreeTwoPairedEightRow22NaturalModule.dualUniform
  · change UniformSubrepresentationGeneratorBound
      PrimitiveAffineDegreeTwoPairedEightRow23NaturalModule.representation.dual 1
    exact PrimitiveAffineDegreeTwoPairedEightRow23NaturalModule.dualUniform
  · change UniformSubrepresentationGeneratorBound
      PrimitiveAffineDegreeTwoPairedEightRow24NaturalModule.representation.dual 1
    exact PrimitiveAffineDegreeTwoPairedEightRow24NaturalModule.dualUniform

theorem naturalCapacity_two_iff (j : Fin 24) :
    naturalCapacity j=2 ↔ IsModuleTwoRow j := by
  fin_cases j <;> simp only [IsModuleTwoRow] <;> decide

theorem naturalCapacity_one_or_two (j : Fin 24) :
    naturalCapacity j=1 ∨ naturalCapacity j=2 := by
  fin_cases j <;> decide

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops
