import SymmetricSubgroupAsymptotics.CFSGAlternatingSylowGeneration
import SymmetricSubgroupAsymptotics.CFSGAlternatingSylowSelfNormalizer
import Mathlib.GroupTheory.Nilpotent

/-! The original alternating group in every classifier degree has an actual
Sylow two-subgroup with soluble normalizer and two generating conjugates.
Degree five uses its displayed Klein four; all larger degrees use the
uniform generation and self-normalizer theorems. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGAlternatingGoodSylow

theorem normalizer_soluble {X : Type*} [Fintype X] [DecidableEq X]
    (P : Sylow 2 (alternatingGroup X)) (hn : 6 ≤ Nat.card X) :
    IsSolvable (Subgroup.normalizer (P : Set (alternatingGroup X))) := by
  letI : Group.IsNilpotent (Subgroup.normalizer (P : Set (alternatingGroup X))) :=
    (CFSGAlternatingSylowSelfNormalizer.normalizer_isPGroup P hn).isNilpotent
  infer_instance

theorem goodSylowPrime (n : ℕ) (hn : 5 ≤ n) :
    CFSGReduction.GoodSylowPrime (alternatingGroup (Fin n)) 2 := by
  by_cases hfive : n = 5
  · subst n
    exact CFSGAlternatingFiveGoodSylow.goodSylowPrime
  obtain ⟨P, g, hgen⟩ := CFSGAlternatingSylowGeneration.exists_generating_conjugates n hn
  refine ⟨Nat.prime_two, P, g, ?_, hgen⟩
  exact normalizer_soluble P (by simpa only [Nat.card_fin] using (show 6 ≤ n by omega))

end SymmetricSubgroupAsymptotics.CFSGAlternatingGoodSylow
