import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Quadratic descent coordinates from a genuine nonfixed element.
The difference quotient works in characteristic two as well; no trace
division or supplied quadratic-field basis is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticFixedCoefficients
variable {K : Type*} [Field K]

theorem exists_fixed_coefficients (sigma : K ≃+* K)
    (hsigma : ∀ a, sigma (sigma a) = a) (theta : K) (htheta : sigma theta ≠ theta) (a : K) :
    ∃ c d : K, sigma c = c ∧ sigma d = d ∧ a = c + theta * d := by
  let d := (a - sigma a) / (theta - sigma theta)
  have hd0 : theta - sigma theta ≠ 0 := sub_ne_zero.mpr (Ne.symm htheta)
  have hd : d * (theta - sigma theta) = a - sigma a := div_mul_cancel₀ _ hd0
  have hsd : sigma d = d := by
    dsimp only [d]
    rw [map_div₀, map_sub, map_sub, hsigma a, hsigma theta]
    have hn : sigma a - a = -(a - sigma a) := by ring
    have ht : sigma theta - theta = -(theta - sigma theta) := by ring
    rw [hn, ht, neg_div_neg_eq]
  have hsc : sigma (a - theta * d) = a - theta * d := by
    rw [map_sub, map_mul, hsd]
    linear_combination hd
  exact ⟨a - theta * d, d, hsc, hsd, by ring⟩

theorem exists_subfield_coefficients (sigma : K ≃+* K)
    (hsigma : ∀ a, sigma (sigma a) = a) (theta : K) (htheta : sigma theta ≠ theta)
    (F : Subfield K) (hF : ∀ a, a ∈ F ↔ sigma a = a) (a : K) :
    ∃ c d : F, a = c.val + theta * d.val := by
  obtain ⟨c, d, hc, hd, he⟩ := exists_fixed_coefficients sigma hsigma theta htheta a
  exact ⟨⟨c, (hF c).mpr hc⟩, ⟨d, (hF d).mpr hd⟩, he⟩

end SymmetricSubgroupAsymptotics.CFSGQuadraticFixedCoefficients
