import SymmetricSubgroupAsymptotics.BinaryActionCoverage8
import Mathlib.Tactic.NormNum
import SymmetricSubgroupAsymptotics.BinaryDegreeEightRegistryGroupFacts
import SymmetricSubgroupAsymptotics.S8CompletedHigherSeedCanonicalCoverage
import SymmetricSubgroupAsymptotics.S8Seed26OvergroupCoverage
import SymmetricSubgroupAsymptotics.S8Seed29CanonicalCoverage
import SymmetricSubgroupAsymptotics.S8Seed30OvergroupCoverage
import SymmetricSubgroupAsymptotics.S8Seed31OvergroupCoverage

/-! All already covered binary seeds of order at least64 dispatch through
the original-point binary registry. The original subgroup, its inclusion
and its actual point conjugator are retained. Nonbinary U is necessary:
a binary seed itself has no row in the24 nonbinary catalogue. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8LargerBinarySeedCanonicalCoverage
abbrev Ambient := Equiv.Perm (Fin 8)

theorem complete (U P : Subgroup Ambient) (hPU : P ≤ U)
    (hP : IsPGroup 2 P) (htrans : PermutationSubgroupTransitive P)
    (h32 : 32 < Nat.card P) (hnot : ¬ IsPGroup 2 U) :
    ∃ i : Fin 24, ∃ c : Ambient,
      MulAut.conj c • U = Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.canonical i := by
  obtain ⟨i, c, hc⟩ := BinaryActionRegistry8.complete P hP htrans
  have hcard : Nat.card P = Nat.card (BinaryActionRegistry8.actions i) :=
    Nat.card_congr ((Subgroup.equivSMul (MulAut.conj c) P).trans
      (MulEquiv.subgroupCongr hc)).toEquiv
  have hlarge : 32 < 2 ^ BinaryDegreeEightRegistryGroupFacts.exponent i := by
    rw [← BinaryDegreeEightRegistryGroupFacts.card_pow, ← hcard]
    exact h32
  fin_cases i
  all_goals norm_num [BinaryDegreeEightRegistryGroupFacts.exponent] at hlarge
  · exact S8Seed26OvergroupCoverage.canonical_complete_of_conjugate U P hPU c hc hnot
  · exact S8CompletedHigherSeedCanonicalCoverage.seed27 U P hPU c hc hnot
  · exact S8CompletedHigherSeedCanonicalCoverage.seed28 U P hPU c hc hnot
  · exact S8Seed29CanonicalCoverage.complete_of_conjugate U P hPU c hc hnot
  · exact S8Seed30OvergroupCoverage.canonical_complete_of_conjugate U P hPU c hc hnot
  · exact S8Seed31OvergroupCoverage.canonical_complete_of_conjugate U P hPU c hc hnot
  · exact S8CompletedHigherSeedCanonicalCoverage.seed128 U P hPU c hc hnot

end SymmetricSubgroupAsymptotics.S8LargerBinarySeedCanonicalCoverage
end
