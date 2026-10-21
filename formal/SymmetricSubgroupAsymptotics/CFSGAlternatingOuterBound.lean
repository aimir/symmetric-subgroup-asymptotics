import SymmetricSubgroupAsymptotics.CFSGAlternatingConjugacyStabilizer
import SymmetricSubgroupAsymptotics.CFSGAlternatingSixConjugacyOrbit
import SymmetricSubgroupAsymptotics.CFSGAlternatingMinimumIndex
import Mathlib.Tactic.Linarith

/-! The uniform alternating-family outer bound, retaining the genuine
exceptional degree-six factor. No additional classification premise is
used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGAlternatingOuterBound
open PrimitiveSocleRawStructure CFSGAlternatingOuterAutomorphisms
open CFSGAlternatingThreeCyclePreservation CFSGAlternatingConjugacyStabilizer
open CFSGAlternatingMinimumIndex

/-- Outside degree six, every automorphism is actual point conjugation. -/
theorem permutationConjugation_range_eq_top (n : ℕ) (hn : 5≤n) (hne : n≠6) :
    (permutationConjugation n).range=⊤ := by
  apply top_unique
  intro f _
  obtain ⟨σ,hσ⟩ := exists_permutation_conjugation_fin n hn f
    (map_isThreeCycle n hn hne f)
  exact ⟨σ,hσ.symm⟩

/-- The exceptional factor is at most two, because there are only two
actual order-three conjugacy classes in degree six. -/
theorem permutationConjugation_index_le_two (n : ℕ) (hn : 5≤n) :
    (permutationConjugation n).range.index≤2 := by
  by_cases he : n=6
  · subst n
    rw [permutationConjugation_range_eq_stabilizer 6 (by decide)
      CFSGAlternatingSixConjugacyOrbit.single
      CFSGAlternatingSixConjugacyOrbit.single_isThreeCycle]
    exact CFSGAlternatingSixConjugacyOrbit.conjugacy_stabilizer_index_le_two
  · rw [permutationConjugation_range_eq_top n hn he]
    simp

theorem outer_card_le_four (n : ℕ) (hn : 5≤n) : Nat.card (Outer (A n))≤4 := by
  rw [outer_card_eq_two_mul_permutationConjugation_index n hn]
  have hi := permutationConjugation_index_le_two n hn
  omega

theorem outer_card_eq_two_of_ne_six (n : ℕ) (hn : 5≤n) (hne : n≠6) :
    Nat.card (Outer (A n))=2 := by
  rw [outer_card_eq_two_mul_permutationConjugation_index n hn,
    permutationConjugation_range_eq_top n hn hne]
  simp

/-- The precise family inequality required by PublishedSimpleIndexBounds. -/
theorem outer_card_le_three_logb (n : ℕ) (hn : 5≤n) :
    (Nat.card (Outer (A n)) : ℝ)≤3*Real.logb 2 n := by
  have hc : (Nat.card (Outer (A n)) : ℝ)≤4 := by exact_mod_cast outer_card_le_four n hn
  have hn4 : ((2 : ℝ)^2)≤n := by
    norm_num
    exact_mod_cast (by omega : 4≤n)
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
    (by norm_num : (0 : ℝ)<2^2) hn4
  simp only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2),mul_one] at hl
  norm_num at hl
  linarith

/-- Complete least-index/order/outer receipt for the literal alternating
family, suitable for direct use after concrete CFSG classification. -/
theorem simpleIndexBounds (n : ℕ) (hn : 5≤n) (ell : ℕ)
    (hell : LeastProperIndex (A n) ell) :
    ell^2<Nat.card (A n) ∧ (Nat.card (Outer (A n)) : ℝ)≤3*Real.logb 2 ell := by
  have he := leastProperIndex_eq_degree n hn ell hell
  subst ell
  exact ⟨degree_square_lt_card n hn,outer_card_le_three_logb n hn⟩

end SymmetricSubgroupAsymptotics.CFSGAlternatingOuterBound
