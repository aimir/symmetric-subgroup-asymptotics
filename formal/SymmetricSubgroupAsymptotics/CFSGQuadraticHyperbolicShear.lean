import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-! Hyperbolic-pole shears retaining the actual quadratic form in every
characteristic. The parameter norm is Q(z), so division by two is never
used. This supplies companion normalization after fixing a singular
axis, without a classical-group recognition theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticHyperbolicShear
variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]

def norm (Q : QuadraticForm K W) (x : K × (W × K)) : K := x.1 * x.2.2 + Q x.2.1

def transform (Q : QuadraticForm K W) (z : W) (x : K × (W × K)) : K × (W × K) :=
  (x.1 - QuadraticMap.polar Q z x.2.1 - Q z * x.2.2,
    (x.2.1 + x.2.2 • z, x.2.2))

theorem transform_zero (Q : QuadraticForm K W) (x : K × (W × K)) :
    transform Q 0 x = x := by
  rcases x with ⟨a, w, b⟩
  simp [transform]

theorem transform_comp (Q : QuadraticForm K W) (z t : W) (x : K × (W × K)) :
    transform Q z (transform Q t x) = transform Q (z + t) x := by
  apply Prod.ext
  · dsimp only [transform]
    rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
      QuadraticMap.polar_add_left, QuadraticMap.map_add Q z t]
    simp only [smul_eq_mul]
    ring
  · apply Prod.ext
    · dsimp only [transform]
      module
    · rfl

theorem transform_preserves (Q : QuadraticForm K W) (z : W) (x : K × (W × K)) :
    norm Q (transform Q z x) = norm Q x := by
  dsimp only [norm, transform]
  rw [QuadraticMap.map_add Q x.2.1 (x.2.2 • z), Q.map_smul, QuadraticMap.polar_smul_right,
    QuadraticMap.polar_comm Q x.2.1 z]
  simp only [smul_eq_mul]
  ring

def transformLinear (Q : QuadraticForm K W) (z : W) :
    (K × (W × K)) →ₗ[K] (K × (W × K)) where
  toFun := transform Q z
  map_add' x y := by
    apply Prod.ext
    · change (x.1 + y.1) - QuadraticMap.polar Q z (x.2.1 + y.2.1) -
        Q z * (x.2.2 + y.2.2) =
          (x.1 - QuadraticMap.polar Q z x.2.1 - Q z * x.2.2) +
          (y.1 - QuadraticMap.polar Q z y.2.1 - Q z * y.2.2)
      rw [QuadraticMap.polar_add_right]
      ring
    · apply Prod.ext
      · change (x.2.1 + y.2.1) + (x.2.2 + y.2.2) • z =
          (x.2.1 + x.2.2 • z) + (y.2.1 + y.2.2 • z)
        module
      · rfl
  map_smul' a x := by
    apply Prod.ext
    · change a * x.1 - QuadraticMap.polar Q z (a • x.2.1) - Q z * (a * x.2.2) =
        a * (x.1 - QuadraticMap.polar Q z x.2.1 - Q z * x.2.2)
      rw [QuadraticMap.polar_smul_right]
      simp only [smul_eq_mul]
      ring
    · apply Prod.ext
      · change a • x.2.1 + (a * x.2.2) • z = a • (x.2.1 + x.2.2 • z)
        module
      · rfl

def transformEquiv (Q : QuadraticForm K W) (z : W) :
    (K × (W × K)) ≃ₗ[K] (K × (W × K)) where
  toLinearMap := transformLinear Q z
  invFun := transform Q (-z)
  left_inv x := by
    change transform Q (-z) (transform Q z x) = x
    rw [transform_comp, neg_add_cancel, transform_zero]
  right_inv x := by
    change transform Q z (transform Q (-z) x) = x
    rw [transform_comp, add_neg_cancel, transform_zero]

theorem transform_fix_axis (Q : QuadraticForm K W) (z : W) :
    transform Q z (1, (0, 0)) = (1, (0, 0)) := by
  simp [transform]

theorem normalize_companion (Q : QuadraticForm K W) (x : K × (W × K))
    (hy : x.2.2 = 1) (hQ : norm Q x = 0) :
    transform Q (-x.2.1) x = (0, (0, 1)) := by
  have hw : (transform Q (-x.2.1) x).2.1 = 0 := by
    simp only [transform, hy, one_smul, add_neg_cancel]
  have hn := (transform_preserves Q (-x.2.1) x).trans hQ
  have ha : (transform Q (-x.2.1) x).1 = 0 := by
    change (transform Q (-x.2.1) x).1 * x.2.2 +
      Q (transform Q (-x.2.1) x).2.1 = 0 at hn
    rw [hw, QuadraticMap.map_zero, add_zero, hy, mul_one] at hn
    exact hn
  apply Prod.ext
  · exact ha
  · apply Prod.ext
    · exact hw
    · exact hy

end SymmetricSubgroupAsymptotics.CFSGQuadraticHyperbolicShear
