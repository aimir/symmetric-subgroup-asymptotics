import SymmetricSubgroupAsymptotics.S8AboveSixteenBinarySeedCanonicalCoverage
import SymmetricSubgroupAsymptotics.S8Seed6CanonicalCoverage
import SymmetricSubgroupAsymptotics.S8Seed7CanonicalCoverage
import SymmetricSubgroupAsymptotics.S8Seed8CanonicalCoverage
import SymmetricSubgroupAsymptotics.S8Seed9CanonicalCoverage
import SymmetricSubgroupAsymptotics.S8Seed10CanonicalCoverage
import SymmetricSubgroupAsymptotics.S8Seed11CanonicalCoverage

/-! Exact final finite action dispatch. Every subgroup and point conjugator
is retained. This source has no classification premise; all seed modules
must exist and pass their separate checks before this assembly can compile. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8AboveEightBinarySeedCanonicalCoverage
abbrev Ambient := Equiv.Perm (Fin 8)

theorem complete (U P : Subgroup Ambient) (hPU : P ≤ U)
    (hP : IsPGroup 2 P) (htrans : PermutationSubgroupTransitive P)
    (h8 : 8 < Nat.card P) (hnot : ¬ IsPGroup 2 U) :
    ∃ i : Fin 24, ∃ c : Ambient, MulAut.conj c • U = Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.canonical i := by
  by_cases h16 : 16 < Nat.card P
  · exact S8AboveSixteenBinarySeedCanonicalCoverage.complete U P hPU hP htrans h16 hnot
  obtain ⟨i, c, hc⟩ := BinaryActionRegistry8.complete P hP htrans
  have hcard : Nat.card P = Nat.card (BinaryActionRegistry8.actions i) :=
    Nat.card_congr ((Subgroup.equivSMul (MulAut.conj c) P).trans
      (MulEquiv.subgroupCongr hc)).toEquiv
  have hupp : 2 ^ BinaryDegreeEightRegistryGroupFacts.exponent i ≤ 16 := by
    rw [← BinaryDegreeEightRegistryGroupFacts.card_pow, ← hcard]
    exact le_of_not_gt h16
  have hlow : 8 < 2 ^ BinaryDegreeEightRegistryGroupFacts.exponent i := by
    rw [← BinaryDegreeEightRegistryGroupFacts.card_pow, ← hcard]
    exact h8
  have hrange : 8 < 2 ^ BinaryDegreeEightRegistryGroupFacts.exponent i ∧
      2 ^ BinaryDegreeEightRegistryGroupFacts.exponent i ≤ 16 := ⟨hlow, hupp⟩
  fin_cases i
  all_goals norm_num [BinaryDegreeEightRegistryGroupFacts.exponent] at hrange
  · exact S8Seed6CanonicalCoverage.complete_of_conjugate U P hPU c hc hnot
  · exact S8Seed7CanonicalCoverage.complete_of_conjugate U P hPU c hc hnot
  · exact S8Seed8CanonicalCoverage.complete_of_conjugate U P hPU c hc hnot
  · exact S8Seed9CanonicalCoverage.complete_of_conjugate U P hPU c hc hnot
  · exact S8Seed10CanonicalCoverage.complete_of_conjugate U P hPU c hc hnot
  · exact S8Seed11CanonicalCoverage.complete_of_conjugate U P hPU c hc hnot

end SymmetricSubgroupAsymptotics.S8AboveEightBinarySeedCanonicalCoverage
end
