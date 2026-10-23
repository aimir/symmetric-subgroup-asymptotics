import SymmetricSubgroupAsymptotics.CFSGSesquilinearKernelRigidity
import Mathlib.LinearAlgebra.Basis.Defs

/-! A semilinear equivalence preserving all zero-pairing tests of a
nondegenerate sesquilinear duality has a single nonzero multiplier.
Its field automorphism commutes with the duality's field automorphism;
this compatibility is proved, rather than assumed. Signed Hermitian
forms are included without choosing a skew-Hermitian normalization. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSesquilinearSimilitudeRigidity
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
local instance (s : K ≃+* K) : RingHomInvPair s.toRingHom s.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv s
local instance (s : K ≃+* K) : RingHomInvPair s.symm.toRingHom s.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm s

def pulledDual (tau : K ≃+* K)
    (D : (I → K) ≃+ Module.Dual K (I → K))
    (e : (I → K) ≃ₛₗ[tau.toRingHom] (I → K)) :
    (I → K) →+ Module.Dual K (I → K) where
  toFun v := {
    toFun := fun w => tau.symm (D (e v) (e w))
    map_add' := by intro w z; simp only [map_add]
    map_smul' := by
      intro a w
      change tau.symm (D (e v) (e (a • w))) = a * tau.symm (D (e v) (e w))
      rw [map_smulₛₗ, map_smul]
      change tau.symm (tau a * D (e v) (e w)) = _
      rw [map_mul, tau.symm_apply_apply] }
  map_zero' := by
    apply LinearMap.ext
    intro w
    change tau.symm (D (e 0) (e w)) = 0
    simp only [map_zero, LinearMap.zero_apply]
  map_add' v z := by
    apply LinearMap.ext
    intro w
    change tau.symm (D (e (v + z)) (e w)) =
      tau.symm (D (e v) (e w)) + tau.symm (D (e z) (e w))
    simp only [map_add, LinearMap.add_apply]

omit [Fintype I] [DecidableEq I] in
theorem pulledDual_smul (sigma tau : K ≃+* K)
    (D : (I → K) ≃+ Module.Dual K (I → K))
    (hD : ∀ (a : K) (v : I → K), D (a • v) = sigma a • D v)
    (e : (I → K) ≃ₛₗ[tau.toRingHom] (I → K)) (a : K) (v : I → K) :
    pulledDual tau D e (a • v) =
      ((tau.trans sigma).trans tau.symm) a • pulledDual tau D e v := by
  apply LinearMap.ext
  intro w
  change tau.symm (D (e (a • v)) (e w)) =
    tau.symm (sigma (tau a)) * tau.symm (D (e v) (e w))
  rw [map_smulₛₗ, hD]
  change tau.symm (sigma (tau a) * D (e v) (e w)) = _
  exact map_mul _ _ _

theorem exists_multiplier_and_field_commute (sigma tau : K ≃+* K)
    (D : (I → K) ≃+ Module.Dual K (I → K))
    (hD : ∀ (a : K) (v : I → K), D (a • v) = sigma a • D v)
    (e : (I → K) ≃ₛₗ[tau.toRingHom] (I → K))
    (he : ∀ (v w : I → K), D (e v) (e w) = 0 ↔ D v w = 0)
    (i₀ i₁ : I) (hne : i₀ ≠ i₁) :
    ∃ c : K, c ≠ 0 ∧
      (∀ v w, D (e v) (e w) = c * tau (D v w)) ∧ Function.Commute sigma tau := by
  have hker (v w : I → K) : pulledDual tau D e v w = 0 ↔ D v w = 0 := by
    change tau.symm (D (e v) (e w)) = 0 ↔ D v w = 0
    exact (tau.symm.map_eq_zero_iff).trans (he v w)
  obtain ⟨c, hc, hform, hfield⟩ := CFSGSesquilinearKernelRigidity.common_scalar_and_field
    sigma ((tau.trans sigma).trans tau.symm) D (pulledDual tau D e)
    hD (pulledDual_smul sigma tau D hD e) hker i₀ i₁ hne
  refine ⟨tau c, (map_ne_zero tau).mpr hc, ?_, ?_⟩
  · intro v w
    have hh := congrArg (fun f : Module.Dual K (I → K) => tau (f w)) (hform v)
    change tau (tau.symm (D (e v) (e w))) = tau (c * D v w) at hh
    simpa only [tau.apply_symm_apply, map_mul] using hh
  · intro a
    have hh := congrArg (fun s : K ≃+* K => tau (s a)) hfield
    change tau (sigma a) = tau (tau.symm (sigma (tau a))) at hh
    exact (hh.trans (tau.apply_symm_apply _)).symm

end SymmetricSubgroupAsymptotics.CFSGSesquilinearSimilitudeRigidity
