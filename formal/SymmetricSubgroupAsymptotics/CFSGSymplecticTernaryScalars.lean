import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Ring

/-! Scalar saturation for literal additive root lines over a field of
cardinality three. No choice of an isomorphism with `ZMod 3` is needed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticTernaryScalars

theorem scalar_cases {K : Type} [Field K] [Finite K]
    (hcard : Nat.card K = 3) (a : K) : a = 0 ∨ a = 1 ∨ a = -1 := by
  letI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 3 := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have hp : a ^ 3 = a := by simpa only [hc] using FiniteField.pow_card a
  have hz : a * (a - 1) * (a + 1) = 0 := by
    calc
      a * (a - 1) * (a + 1) = a ^ 3 - a := by ring
      _ = 0 := sub_eq_zero.mpr hp
  rcases mul_eq_zero.mp hz with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h))

theorem root_line_mem {K G : Type} [Field K] [Finite K] [Group G]
    (hcard : Nat.card K = 3) (f : K → G)
    (hf0 : f 0 = 1) (hfadd : ∀ a b, f (a + b) = f a * f b)
    (H : Subgroup G) (h1 : f 1 ∈ H) : ∀ a, f a ∈ H := by
  have hn : f (-1) = (f 1)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← hfadd, neg_add_cancel, hf0]
  intro a
  rcases scalar_cases hcard a with ha | ha | ha
  · rw [ha, hf0]
    exact H.one_mem
  · exact ha ▸ h1
  · rw [ha, hn]
    exact H.inv_mem h1

theorem extraction_coefficient {K : Type} [Field K] [Finite K]
    (hcard : Nat.card K = 3) :
    (1 - ((-1 : Kˣ) : K)) * (1 - ((-1 : Kˣ) : K)⁻¹) = 1 := by
  letI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 3 := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have hthree : (3 : K) = 0 := by
    simpa only [hc] using FiniteField.cast_card_eq_zero K
  simp only [Units.val_neg, Units.val_one, inv_neg, inv_one]
  calc
    (1 - (-1 : K)) * (1 - (-1 : K)) = 1 + (3 : K) := by ring
    _ = 1 := by rw [hthree, add_zero]

end SymmetricSubgroupAsymptotics.CFSGSymplecticTernaryScalars
