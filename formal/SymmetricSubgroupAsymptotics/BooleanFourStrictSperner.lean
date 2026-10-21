import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Equality in the four-dimensional Boolean Sperner bound is rigid.
The proof uses LYM and five scalar binomial coefficients; it does not
enumerate families of subsets. -/
set_option autoImplicit false
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics

private theorem boolean_four_reciprocal_choose_bound (s : Finset (Fin 4)) :
    (1 : ℚ) / 6 ≤ ((4).choose s.card : ℚ)⁻¹ := by
  have hc : s.card ≤ 4 := (Finset.card_le_univ s).trans_eq (Fintype.card_fin 4)
  have hcases : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 ∨ s.card = 3 ∨ s.card = 4 := by omega
  rcases hcases with h | h | h | h | h <;> norm_num [h, Nat.choose]

private theorem boolean_four_reciprocal_choose_strict
    (s : Finset (Fin 4)) (hne : s.card ≠ 2) :
    (1 : ℚ) / 6 < ((4).choose s.card : ℚ)⁻¹ := by
  have hc : s.card ≤ 4 := (Finset.card_le_univ s).trans_eq (Fintype.card_fin 4)
  have hcases : s.card = 0 ∨ s.card = 1 ∨ s.card = 3 ∨ s.card = 4 := by omega
  rcases hcases with h | h | h | h <;> norm_num [h, Nat.choose]

/-- Every member of a six-element Boolean-four antichain has rank two. -/
theorem boolean_four_antichain_card_six_member_card
    (A : Finset (Finset (Fin 4)))
    (hA : IsAntichain (· ⊆ ·) (A : Set (Finset (Fin 4))))
    (hcard : A.card = 6) (s : Finset (Fin 4)) (hs : s ∈ A) : s.card = 2 := by
  by_contra hne
  have hlt : (∑ _t ∈ A, (1 : ℚ) / 6) < ∑ t ∈ A, ((4).choose t.card : ℚ)⁻¹ :=
    Finset.sum_lt_sum (fun t _ => boolean_four_reciprocal_choose_bound t)
      ⟨s, hs, boolean_four_reciprocal_choose_strict s hne⟩
  have hlym : (∑ t ∈ A, ((4).choose t.card : ℚ)⁻¹) ≤ 1 := by
    simpa only [Fintype.card_fin] using
      (Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose (𝕜 := ℚ) hA)
  have hone : (∑ _t ∈ A, (1 : ℚ) / 6) = 1 := by
    simp only [Finset.sum_const, hcard]
    norm_num
  rw [hone] at hlt
  exact (not_lt_of_ge hlym) hlt

/-- The full equality family is exactly the literal middle layer. -/
theorem boolean_four_antichain_card_six_eq_middle
    (A : Finset (Finset (Fin 4)))
    (hA : IsAntichain (· ⊆ ·) (A : Set (Finset (Fin 4))))
    (hcard : A.card = 6) : A = Finset.univ.powersetCard 2 := by
  have hsub : A ⊆ Finset.univ.powersetCard 2 := by
    intro s hs
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ s, boolean_four_antichain_card_six_member_card A hA hcard s hs⟩
  apply Finset.eq_of_subset_of_card_le hsub
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, hcard]
  decide

end SymmetricSubgroupAsymptotics
