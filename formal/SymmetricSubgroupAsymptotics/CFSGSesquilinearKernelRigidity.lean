import SymmetricSubgroupAsymptotics.CFSGAdditiveLinePreservingMap
import SymmetricSubgroupAsymptotics.CFSGLinearFunctionalKernels

/-! Two nondegenerate sesquilinear dualities with the same literal
zero-pairing tests have a common nonzero multiplier and the same field
component. No involution, characteristic or finite-field premise is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSesquilinearKernelRigidity
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

theorem common_scalar_and_field
    (sigma tau : K ≃+* K)
    (D : (I → K) ≃+ Module.Dual K (I → K))
    (F : (I → K) →+ Module.Dual K (I → K))
    (hD : ∀ (a : K) (v : I → K), D (a • v) = sigma a • D v)
    (hF : ∀ (a : K) (v : I → K), F (a • v) = tau a • F v)
    (hker : ∀ (v w : I → K), F v w = 0 ↔ D v w = 0)
    (i₀ i₁ : I) (hne : i₀ ≠ i₁) :
    ∃ c : K, c ≠ 0 ∧ (∀ v, F v = c • D v) ∧ sigma = tau := by
  classical
  have hFne (v : I → K) (hv : v ≠ 0) : F v ≠ 0 := by
    intro hz
    apply hv
    apply D.injective
    rw [map_zero]
    apply LinearMap.ext
    intro w
    exact (hker v w).mp (by rw [hz]; rfl)
  have hsymm (a : K) (v : I → K) : D.symm (a • D v) = sigma.symm a • v := by
    apply D.injective
    rw [D.apply_symm_apply, hD, sigma.apply_symm_apply]
  let T : (I → K) →+ (I → K) := D.symm.toAddMonoidHom.comp F
  have hT (v : I → K) : ∃ a : K, T v = a • v := by
    by_cases hv : v = 0
    · subst v
      exact ⟨0, by rw [map_zero, zero_smul]⟩
    · obtain ⟨a, _, ha⟩ := CFSGLinearFunctionalKernels.nonzero_smul_of_zero_iff
        (F v) (D v) (hFne v hv) (hker v)
      refine ⟨sigma.symm a, ?_⟩
      change D.symm (F v) = _
      rw [ha, hsymm]
  obtain ⟨a, ha⟩ := CFSGAdditiveLinePreservingMap.exists_scalar T hT i₀ i₁ hne
  have hform (v : I → K) : F v = sigma a • D v := by
    have hh := congrArg D (ha v)
    change D (D.symm (F v)) = D (a • v) at hh
    rwa [D.apply_symm_apply, hD] at hh
  let v₀ : I → K := Pi.single i₀ 1
  have hv₀ : v₀ ≠ 0 := by
    intro h
    have hh := congrFun h i₀
    simp [v₀] at hh
  have hDv : D v₀ ≠ 0 := by
    intro hz
    exact hv₀ (D.injective (hz.trans D.map_zero.symm))
  obtain ⟨w₀, hw₀⟩ : ∃ w : I → K, D v₀ w ≠ 0 := by
    by_contra h
    apply hDv
    apply LinearMap.ext
    intro w
    exact not_ne_iff.mp (not_exists.mp h w)
  have hc : sigma a ≠ 0 := by
    intro hz
    apply hFne v₀ hv₀
    rw [hform, hz, zero_smul]
  refine ⟨sigma a, hc, hform, ?_⟩
  apply RingEquiv.ext
  intro b
  have hh := hF b v₀
  rw [hform, hform, hD] at hh
  have he := congrArg (fun f : Module.Dual K (I → K) => f w₀) hh
  have he' : (sigma a * D v₀ w₀) * sigma b = (sigma a * D v₀ w₀) * tau b := by
    simpa only [LinearMap.smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using he
  exact mul_left_cancel₀ (mul_ne_zero hc hw₀) he'

end SymmetricSubgroupAsymptotics.CFSGSesquilinearKernelRigidity
