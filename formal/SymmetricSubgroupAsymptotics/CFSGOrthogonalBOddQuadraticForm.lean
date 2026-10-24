import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGramNondegenerate
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic.Ring

/-! The actual odd-B quadratic form is half its original Gram norm.
Its polar form is exactly the original preserved Gram form; the factor
two is explicit and never discarded in the hyperbolic coordinates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOddQuadraticForm

open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBIntrinsicLongRoots
open CFSGOrthogonalBUnipotent
variable (K : Type) [Field K]

def quadratic (n : ℕ) : QuadraticForm K (Index n → K) :=
  (2 : K)⁻¹ • LinearMap.BilinMap.toQuadraticMap (gram K n).toBilin'

theorem quadratic_apply (n : ℕ) (v : Index n → K) :
    quadratic K n v = (2 : K)⁻¹ * (gram K n).toBilin' v v := rfl

theorem quadratic_polar [Finite K] (h2 : (2 : K) ≠ 0) (n : ℕ) (v w : Index n → K) :
    (quadratic K n).polarBilin v w = (gram K n).toBilin' v w := by
  change quadratic K n (v + w) - quadratic K n v - quadratic K n w = _
  rw [quadratic_apply, quadratic_apply, quadratic_apply]
  simp only [map_add, LinearMap.add_apply]
  rw [gram_pairing_symmetric n w v]
  calc
    _ = ((2 : K)⁻¹ * 2) * (gram K n).toBilin' v w := by ring
    _ = _ := by rw [inv_mul_cancel₀ h2, one_mul]

theorem quadratic_nondegenerate [Finite K] (h2 : (2 : K) ≠ 0) (n : ℕ) :
    (quadratic K n).polarBilin.Nondegenerate := by
  have he : (quadratic K n).polarBilin = (gram K n).toBilin' :=
    LinearMap.ext₂ (quadratic_polar K h2 n)
  rw [he]
  exact gram_nondegenerate h2 n

theorem elementary_preserves_quadratic (h2 : (2 : K) ≠ 0) (n : ℕ)
    (g : elementaryRootGroup K n) (v : Index n → K) :
    quadratic K n ((g.val : Mat K n) *ᵥ v) = quadratic K n v := by
  rw [quadratic_apply, quadratic_apply, natural_pairing_invariant h2 n g v v]

theorem quadratic_eq_zero_iff (h2 : (2 : K) ≠ 0) (n : ℕ) (v : Index n → K) :
    quadratic K n v = 0 ↔ (gram K n).toBilin' v v = 0 := by
  rw [quadratic_apply]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero h2)
  · intro h
    rw [h, mul_zero]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOddQuadraticForm
