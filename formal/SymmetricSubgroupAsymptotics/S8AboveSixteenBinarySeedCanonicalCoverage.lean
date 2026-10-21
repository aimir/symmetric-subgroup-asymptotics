import SymmetricSubgroupAsymptotics.S8LargerBinarySeedCanonicalCoverage
import SymmetricSubgroupAsymptotics.S8Seed15OvergroupCoverage
import SymmetricSubgroupAsymptotics.S8Seed16OvergroupCoverage
import SymmetricSubgroupAsymptotics.S8Seed17OvergroupCoverage
import SymmetricSubgroupAsymptotics.S8Seed18CanonicalCoverage
import SymmetricSubgroupAsymptotics.S8Seed19OvergroupCoverage
import SymmetricSubgroupAsymptotics.S8Seed20OvergroupCoverage
import SymmetricSubgroupAsymptotics.S8Seed21OvergroupCoverage
import SymmetricSubgroupAsymptotics.S8Seed22CanonicalCoverage

/-! Exact higher-seed dispatch for the next finite frontier. An actual
transitive binary P≤U above order16 is retained throughout. Sources above
order32 use the existing dispatcher; exact binary registry orders leave
the eight already covered order32 action rows for the remaining case. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8AboveSixteenBinarySeedCanonicalCoverage
abbrev Ambient := Equiv.Perm (Fin 8)

theorem complete (U P : Subgroup Ambient) (hPU : P ≤ U)
    (hP : IsPGroup 2 P) (htrans : PermutationSubgroupTransitive P)
    (h16 : 16 < Nat.card P) (hnot : ¬ IsPGroup 2 U) :
    ∃ i : Fin 24, ∃ c : Ambient,
      MulAut.conj c • U = Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.canonical i := by
  by_cases h32 : 32 < Nat.card P
  · exact S8LargerBinarySeedCanonicalCoverage.complete U P hPU hP htrans h32 hnot
  obtain ⟨i, c, hc⟩ := BinaryActionRegistry8.complete P hP htrans
  have hcard : Nat.card P = Nat.card (BinaryActionRegistry8.actions i) :=
    Nat.card_congr ((Subgroup.equivSMul (MulAut.conj c) P).trans
      (MulEquiv.subgroupCongr hc)).toEquiv
  have hlow : 16 < 2 ^ BinaryDegreeEightRegistryGroupFacts.exponent i := by
    rw [← BinaryDegreeEightRegistryGroupFacts.card_pow, ← hcard]
    exact h16
  have hupp : 2 ^ BinaryDegreeEightRegistryGroupFacts.exponent i ≤ 32 := by
    rw [← BinaryDegreeEightRegistryGroupFacts.card_pow, ← hcard]
    exact le_of_not_gt h32
  have hrange : 16 < 2 ^ BinaryDegreeEightRegistryGroupFacts.exponent i ∧
      2 ^ BinaryDegreeEightRegistryGroupFacts.exponent i ≤ 32 := ⟨hlow, hupp⟩
  fin_cases i
  all_goals norm_num [BinaryDegreeEightRegistryGroupFacts.exponent] at hrange
  · exact S8Seed15OvergroupCoverage.canonical_complete_of_conjugate U P hPU c hc hnot
  · exact S8Seed16OvergroupCoverage.canonical_complete_of_conjugate U P hPU c hc hnot
  · exact S8Seed17OvergroupCoverage.canonical_complete_of_conjugate U P hPU c hc hnot
  · exact S8Seed18CanonicalCoverage.complete_of_conjugate U P hPU c hc hnot
  · exact S8Seed19OvergroupCoverage.canonical_complete_of_conjugate U P hPU c hc hnot
  · exact S8Seed20OvergroupCoverage.canonical_complete_of_conjugate U P hPU c hc hnot
  · exact S8Seed21OvergroupCoverage.canonical_complete_of_conjugate U P hPU c hc hnot
  · exact S8Seed22CanonicalCoverage.complete_of_conjugate U P hPU c hc hnot

end SymmetricSubgroupAsymptotics.S8AboveSixteenBinarySeedCanonicalCoverage
end
