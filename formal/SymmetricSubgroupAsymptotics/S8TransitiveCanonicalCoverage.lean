import SymmetricSubgroupAsymptotics.DegreeEightTransitiveBinarySubgroup
import SymmetricSubgroupAsymptotics.BinaryDegreeEightRegistryGroupFacts
import SymmetricSubgroupAsymptotics.S8AboveEightBinarySeedCanonicalCoverage
import SymmetricSubgroupAsymptotics.S8Seed1CanonicalCoverage
import SymmetricSubgroupAsymptotics.S8Seed2CanonicalCoverage
import SymmetricSubgroupAsymptotics.S8Seed3CanonicalCoverage
import SymmetricSubgroupAsymptotics.S8Seed4CanonicalCoverage
import SymmetricSubgroupAsymptotics.S8Seed5CanonicalCoverage
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Exact final finite action dispatch. Every subgroup and point conjugator
is retained. This source has no classification premise; all seed modules
must exist and pass their separate checks before this assembly can compile. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8TransitiveCanonicalCoverage
abbrev Ambient := Equiv.Perm (Fin 8)

theorem complete (U : Subgroup Ambient) (hU : PermutationSubgroupTransitive U)
    (hnot : ¬ IsPGroup 2 U) :
    ∃ i : Fin 24, ∃ c : Ambient, MulAut.conj c • U = Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.canonical i := by
  obtain ⟨P, hPU, hP, htrans⟩ := degreeEight_exists_transitive_binary_subgroup U hU
  by_cases h8 : 8 < Nat.card P
  · exact S8AboveEightBinarySeedCanonicalCoverage.complete U P hPU hP htrans h8 hnot
  obtain ⟨i, c, hc⟩ := BinaryActionRegistry8.complete P hP htrans
  have hcard : Nat.card P = Nat.card (BinaryActionRegistry8.actions i) :=
    Nat.card_congr ((Subgroup.equivSMul (MulAut.conj c) P).trans
      (MulEquiv.subgroupCongr hc)).toEquiv
  have hupp : 2 ^ BinaryDegreeEightRegistryGroupFacts.exponent i ≤ 8 := by
    rw [← BinaryDegreeEightRegistryGroupFacts.card_pow, ← hcard]
    exact le_of_not_gt h8
  fin_cases i
  all_goals norm_num [BinaryDegreeEightRegistryGroupFacts.exponent] at hupp
  · exact S8Seed1CanonicalCoverage.complete_of_conjugate U P hPU c hc hnot
  · exact S8Seed2CanonicalCoverage.complete_of_conjugate U P hPU c hc hnot
  · exact S8Seed3CanonicalCoverage.complete_of_conjugate U P hPU c hc hnot
  · exact S8Seed4CanonicalCoverage.complete_of_conjugate U P hPU c hc hnot
  · exact S8Seed5CanonicalCoverage.complete_of_conjugate U P hPU c hc hnot

theorem publishedClassification : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification := by
  intro U htrans hnot
  exact complete U htrans hnot

end SymmetricSubgroupAsymptotics.S8TransitiveCanonicalCoverage
end
