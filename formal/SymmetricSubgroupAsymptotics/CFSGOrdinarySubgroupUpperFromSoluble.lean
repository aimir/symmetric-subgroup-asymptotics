import SymmetricSubgroupAsymptotics.CFSGNilpotentCountNumerics
import SymmetricSubgroupAsymptotics.CFSGOrdinarySubgroupNumericalClosure
import SymmetricSubgroupAsymptotics.CFSGSolubleOrbitFinal

/-! The ordinary coarse subgroup upper bound needs only the displayed
Aschbacher--Guralnick input; the large-orbit soluble generation step is proved
without either sharp primitive published hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open MarkedC4

theorem ordinarySubgroupUpper_of_soluble_generation
    (hAG : PublishedAschbacherGuralnickSolubleGeneration) :
    OrdinarySubgroupUpper.PublishedTheoremOneUpper := by
  apply CFSGOrdinarySubgroupNumericalClosure.ordinary_upper_of_bounded_nilpotent hAG
  · exact CFSGSolubleOrbitConsequences.publishedProposition62_proved
  · exact CFSGNilpotentCountBudgets.bounded_nilpotent_card

end SymmetricSubgroupAsymptotics.CFSGReduction
