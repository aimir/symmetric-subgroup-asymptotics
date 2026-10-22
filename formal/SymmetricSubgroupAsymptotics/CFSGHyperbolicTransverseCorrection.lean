import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Explicit correction into the complement of a hyperbolic vector.
No Witt extension or group recognition is used: subtracting a multiple
of a singular vector preserves the form on its orthogonal space. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHyperbolicTransverseCorrection
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]

def correction (B : LinearMap.BilinForm K V) (e w : V) (j : W →ₗ[K] V) : W →ₗ[K] V :=
  j - (((B w e)⁻¹) • ((B w).comp j)).smulRight e

theorem correction_apply (B : LinearMap.BilinForm K V) (e w : V) (j : W →ₗ[K] V) (z : W) :
    correction B e w j z = j z - ((B w e)⁻¹ * B w (j z)) • e := rfl

theorem correction_orthogonal (B : LinearMap.BilinForm K V) (e w : V)
    (j : W →ₗ[K] V) (hc : B w e ≠ 0) (z : W) :
    B w (correction B e w j z) = 0 := by
  rw [correction_apply, map_sub, map_smul]
  simp only [smul_eq_mul]
  field_simp [hc] <;> ring

theorem correction_pairing (B : LinearMap.BilinForm K V) (e w : V)
    (j : W →ₗ[K] V) (hee : B e e = 0)
    (he : ∀ z, B e (j z) = 0) (he' : ∀ z, B (j z) e = 0) (z z' : W) :
    B (correction B e w j z) (correction B e w j z') = B (j z) (j z') := by
  simp only [correction_apply, map_sub, LinearMap.sub_apply, map_smul,
    LinearMap.smul_apply, he, he', hee, smul_zero, sub_zero, zero_sub]

theorem correction_leftInverse (B : LinearMap.BilinForm K V) (e w : V)
    (j : W →ₗ[K] V) (π : V →ₗ[K] W) (hj : ∀ z, π (j z) = z) (he : π e = 0) (z : W) :
    π (correction B e w j z) = z := by
  rw [correction_apply, map_sub, map_smul, hj, he, smul_zero, sub_zero]

theorem correction_injective (B : LinearMap.BilinForm K V) (e w : V)
    (j : W →ₗ[K] V) (π : V →ₗ[K] W) (hj : ∀ z, π (j z) = z) (he : π e = 0) :
    Function.Injective (correction B e w j) := by
  intro z z' hz
  have h := congrArg π hz
  simpa only [correction_leftInverse B e w j π hj he] using h

theorem correction_orthogonal_to (B : LinearMap.BilinForm K V) (e w u : V)
    (j : W →ₗ[K] V) (hue : B u e = 0) (huj : ∀ z, B u (j z) = 0) (z : W) :
    B u (correction B e w j z) = 0 := by
  rw [correction_apply, map_sub, map_smul, hue, smul_zero, sub_zero, huj]

end SymmetricSubgroupAsymptotics.CFSGHyperbolicTransverseCorrection
