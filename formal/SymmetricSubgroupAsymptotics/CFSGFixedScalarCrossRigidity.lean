import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Tactic.Ring

/-! A characteristic-free rigidity step for the Hermitian root-star
centroid. Fixed-field coefficients in the crossed equation L(y)x+L(x)y=0
must vanish. No linearity over the fixed field, involution hypothesis,
or division by two is assumed. -/
set_option autoImplicit false
set_option Elab.async false

namespace SymmetricSubgroupAsymptotics.CFSGFixedScalarCrossRigidity
variable {K : Type*} [Field K]

theorem zero_of_cross (sigma : K ≃+* K) (hnonfixed : ∃ t, sigma t ≠ t)
    (L : K → K) (hfixed : ∀ x, sigma (L x) = L x) (hzero : L 0 = 0)
    (hcross : ∀ x y, L y * x + L x * y = 0) : ∀ x, L x = 0 := by
  obtain ⟨t, ht⟩ := hnonfixed
  intro x
  by_cases hx : x = 0
  · simpa only [hx] using hzero
  have h1 : L (x * t) + L x * t = 0 := by
    apply (mul_eq_zero.mp (show x * (L (x * t) + L x * t) = 0 from by
      calc
        _ = L (x * t) * x + L x * (x * t) := by ring
        _ = 0 := hcross x (x * t))).resolve_left hx
  have h2 := congrArg sigma h1
  have h2' : L (x * t) + L x * sigma t = 0 := by
    simpa only [map_add, map_mul, hfixed, map_zero] using h2
  have he : L x * (t - sigma t) = 0 := by
    calc
      _ = (L (x * t) + L x * t) - (L (x * t) + L x * sigma t) := by ring
      _ = 0 := by rw [h1, h2', sub_self]
  exact (mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr ht.symm)

theorem constant_of_polar_coordinates (sigma : K ≃+* K) (hnonfixed : ∃ t, sigma t ≠ t)
    (a : K → K) (hfixed : ∀ x, sigma (a x) = a x)
    (hadd : ∀ x y, a (x + y) + a 0 = a x + a y)
    (hweighted : ∀ x y, a (x + y) * (x + y) = a x * x + a y * y) :
    ∀ x, a x = a 0 := by
  let L : K → K := fun x => a x - a 0
  have hL : ∀ x, sigma (L x) = L x := by
    intro x
    simp only [L, map_sub, hfixed]
  have h0 : L 0 = 0 := sub_self _
  have hc : ∀ x y, L y * x + L x * y = 0 := by
    intro x y
    have ha : a (x + y) = a x + a y - a 0 := eq_sub_iff_add_eq.mpr (hadd x y)
    have hw := hweighted x y
    rw [ha] at hw
    calc
      _ = (a x + a y - a 0) * (x + y) - (a x * x + a y * y) := by dsimp only [L]; ring
      _ = 0 := sub_eq_zero.mpr hw
  intro x
  exact sub_eq_zero.mp (zero_of_cross sigma hnonfixed L hL h0 hc x)

end SymmetricSubgroupAsymptotics.CFSGFixedScalarCrossRigidity
