import SymmetricSubgroupAsymptotics.CFSGNilpotentCountNumerics
import SymmetricSubgroupAsymptotics.CFSGOrdinarySubgroupNumericalClosure
import SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequencesFinal
import SymmetricSubgroupAsymptotics.TraceyRefinedInducedModuleProof

/-! The ordinary coarse subgroup bound is a consequence of the soluble
generation, primitive composition, and primitive normal-generation inputs
already used at the public boundary. Its bounded nilpotent counting step
is proved here through the actual binary/odd physical convolution. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open MarkedC4

theorem ordinarySubgroupUpper_of_retained_inputs
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (hgen : PrimitiveNormalGeneratorInput)
    (hcomp : PrimitiveCompositionLengthInput) :
    OrdinarySubgroupUpper.PublishedTheoremOneUpper := by
  apply CFSGOrdinarySubgroupNumericalClosure.ordinary_upper_of_bounded_nilpotent hAG
  · exact LargeOrbitGeneratorConsequences.publishedProposition62_of_retained_inputs
      hgen traceyRefinedInducedModuleInput_proved hcomp
  · exact CFSGNilpotentCountBudgets.bounded_nilpotent_card

end SymmetricSubgroupAsymptotics.CFSGReduction
