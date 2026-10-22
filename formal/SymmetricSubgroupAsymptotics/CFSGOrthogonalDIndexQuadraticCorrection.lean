import SymmetricSubgroupAsymptotics.CFSGHyperbolicTransverseCorrection
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-! The transverse correction preserves the actual quadratic form,
including characteristic two. Bilinear norm preservation alone would
not imply this statement in characteristic two. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticCorrection
open CFSGHyperbolicTransverseCorrection
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem correction_quadratic (Q : QuadraticForm K V) (e w : V) (j : W →ₗ[K] V)
    (he : Q e = 0) (hje : ∀ z, Q.polarBilin (j z) e = 0) (z : W) :
    Q (correction Q.polarBilin e w j z) = Q (j z) := by
  rw [correction_apply, sub_eq_add_neg, ← neg_smul]
  have h := QuadraticMap.map_add (Q : V → K) (j z)
    ((-((Q.polarBilin w e)⁻¹ * Q.polarBilin w (j z))) • e)
  change Q (j z + (-((Q.polarBilin w e)⁻¹ * Q.polarBilin w (j z))) • e) =
    Q (j z) + Q ((-((Q.polarBilin w e)⁻¹ * Q.polarBilin w (j z))) • e) +
      Q.polarBilin (j z) ((-((Q.polarBilin w e)⁻¹ * Q.polarBilin w (j z))) • e) at h
  simpa only [Q.map_smul, map_smul, he, hje z, smul_eq_mul, mul_zero, add_zero] using h

theorem singular_span_pair (Q : QuadraticForm K V) (u v : V)
    (hu : Q u = 0) (hv : Q v = 0) (huv : Q.polarBilin u v = 0) :
    ∀ x ∈ Submodule.span K {u, v}, Q x = 0 := by
  intro x hx
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  have h := QuadraticMap.map_add (Q : V → K) (a • u) (b • v)
  change Q (a • u + b • v) = Q (a • u) + Q (b • v) + Q.polarBilin (a • u) (b • v) at h
  simpa only [Q.map_smul, map_smul, LinearMap.smul_apply, hu, hv, huv,
    smul_eq_mul, mul_zero, zero_add] using h

theorem singular_sup (Q : QuadraticForm K V) (P R : Submodule K V)
    (hP : ∀ x ∈ P, Q x = 0) (hR : ∀ x ∈ R, Q x = 0)
    (hcross : ∀ x ∈ P, ∀ y ∈ R, Q.polarBilin x y = 0) :
    ∀ x ∈ P ⊔ R, Q x = 0 := by
  intro x hx
  obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.mp hx
  have h := QuadraticMap.map_add (Q : V → K) p r
  change Q (p + r) = Q p + Q r + Q.polarBilin p r at h
  simpa only [hP p hp, hR r hr, hcross p hp r hr, zero_add] using h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticCorrection
