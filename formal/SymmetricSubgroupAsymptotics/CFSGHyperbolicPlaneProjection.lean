import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Literal projection along a hyperbolic pair onto its common
orthogonal complement, with genuine nondegeneracy inherited from the
ambient bilinear form. No Witt decomposition is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHyperbolicPlaneProjection
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (B : LinearMap.BilinForm K V)

def perp (v w : V) : Submodule K V := (B v).ker ⊓ (B w).ker

def projection (v w : V) : V →ₗ[K] V :=
  LinearMap.id - ((B v w)⁻¹ • B w).smulRight v - ((B v w)⁻¹ • B v).smulRight w

theorem projection_apply (v w x : V) : projection B v w x =
    x - ((B v w)⁻¹ * B w x) • v - ((B v w)⁻¹ * B v x) • w := rfl

theorem projection_mem (hs : ∀ x y, B x y = B y x) (v w : V)
    (hv : B v v = 0) (hw : B w w = 0) (hc : B v w ≠ 0) (x : V) :
    projection B v w x ∈ perp B v w := by
  constructor
  · change B v (projection B v w x) = 0
    rw [projection_apply]
    simp only [map_sub, map_smul, smul_eq_mul, hv, mul_zero, sub_zero]
    field_simp [hc]; ring
  · change B w (projection B v w x) = 0
    rw [projection_apply]
    simp only [map_sub, map_smul, smul_eq_mul, hw, mul_zero, sub_zero, hs w v]
    field_simp [hc]; ring

theorem projection_eq_self (v w x : V) (hx : x ∈ perp B v w) : projection B v w x = x := by
  have hv : B v x = 0 := hx.1
  have hw : B w x = 0 := hx.2
  simp only [projection_apply, hv, hw, mul_zero, zero_smul, sub_zero]

theorem pairing_projection (hs : ∀ x y, B x y = B y x) (v w e x : V)
    (he : e ∈ perp B v w) : B e (projection B v w x) = B e x := by
  have hv : B e v = 0 := (hs e v).trans he.1
  have hw : B e w = 0 := (hs e w).trans he.2
  rw [projection_apply]
  simp only [map_sub, map_smul, smul_eq_mul, hv, hw, mul_zero, sub_zero]

theorem perp_nondegenerate (hs : ∀ x y, B x y = B y x)
    (hn : ∀ e, (∀ x, B e x = 0) → e = 0) (v w : V)
    (hv : B v v = 0) (hw : B w w = 0) (hc : B v w ≠ 0)
    (e : V) (he : e ∈ perp B v w) (hz : ∀ x ∈ perp B v w, B e x = 0) : e = 0 := by
  apply hn e
  intro x
  have hp := hz (projection B v w x) (projection_mem B hs v w hv hw hc x)
  rwa [pairing_projection B hs v w e x he] at hp

end SymmetricSubgroupAsymptotics.CFSGHyperbolicPlaneProjection
