import SymmetricSubgroupAsymptotics.CFSGSesquilinearKernelRigidity
import Mathlib.LinearAlgebra.Basis.Defs

/-! Two semilinear coordinate maps on opposed spaces have the SAME
field component when they preserve the literal cross-orthogonality
relation. Dimension two suffices: the argument compares two actual
nondegenerate dualities, not an overlap of dimension at least two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGSesquilinearOpposedFieldCoherence
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
local instance (s : K ≃+* K) : RingHomInvPair s.toRingHom s.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv s
local instance (s : K ≃+* K) : RingHomInvPair s.symm.toRingHom s.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm s

def pulledCrossDual (tauP tauZ : K ≃+* K)
    (D : (I → K) ≃+ Module.Dual K (I → K))
    (eP : (I → K) ≃ₛₗ[tauP.toRingHom] (I → K))
    (eZ : (I → K) ≃ₛₗ[tauZ.toRingHom] (I → K)) :
    (I → K) →+ Module.Dual K (I → K) where
  toFun v := {
    toFun := fun w => tauZ.symm (D (eP v) (eZ w))
    map_add' := by intro w z; simp only [map_add]
    map_smul' := by
      intro a w
      change tauZ.symm (D (eP v) (eZ (a • w))) = a * tauZ.symm (D (eP v) (eZ w))
      rw [map_smulₛₗ, map_smul]
      change tauZ.symm (tauZ a * D (eP v) (eZ w)) = _
      rw [map_mul, tauZ.symm_apply_apply] }
  map_zero' := by
    apply LinearMap.ext
    intro w
    change tauZ.symm (D (eP 0) (eZ w)) = 0
    simp only [map_zero, LinearMap.zero_apply]
  map_add' v z := by
    apply LinearMap.ext
    intro w
    change tauZ.symm (D (eP (v + z)) (eZ w)) =
      tauZ.symm (D (eP v) (eZ w)) + tauZ.symm (D (eP z) (eZ w))
    simp only [map_add, LinearMap.add_apply]

theorem pulledCrossDual_smul (sigma tauP tauZ : K ≃+* K)
    (D : (I → K) ≃+ Module.Dual K (I → K))
    (hD : ∀ (a : K) (v : I → K), D (a • v) = sigma a • D v)
    (eP : (I → K) ≃ₛₗ[tauP.toRingHom] (I → K))
    (eZ : (I → K) ≃ₛₗ[tauZ.toRingHom] (I → K)) (a : K) (v : I → K) :
    pulledCrossDual tauP tauZ D eP eZ (a • v) =
      ((tauP.trans sigma).trans tauZ.symm) a • pulledCrossDual tauP tauZ D eP eZ v := by
  apply LinearMap.ext
  intro w
  change tauZ.symm (D (eP (a • v)) (eZ w)) =
    tauZ.symm (sigma (tauP a)) * tauZ.symm (D (eP v) (eZ w))
  rw [map_smulₛₗ, hD]
  change tauZ.symm (sigma (tauP a) * D (eP v) (eZ w)) = _
  exact map_mul _ _ _

theorem field_eq_of_cross_zero_iff (sigma tauP tauZ : K ≃+* K)
    (D E : (I → K) ≃+ Module.Dual K (I → K))
    (hD : ∀ (a : K) (v : I → K), D (a • v) = sigma a • D v)
    (hE : ∀ (a : K) (v : I → K), E (a • v) = sigma a • E v)
    (eP : (I → K) ≃ₛₗ[tauP.toRingHom] (I → K))
    (eZ : (I → K) ≃ₛₗ[tauZ.toRingHom] (I → K))
    (hzero : ∀ v w, E (eP v) (eZ w) = 0 ↔ D v w = 0)
    (hcomm : Function.Commute sigma tauZ) (i₀ i₁ : I) (hne : i₀ ≠ i₁) :
    tauP = tauZ := by
  have hker (v w : I → K) : pulledCrossDual tauP tauZ E eP eZ v w = 0 ↔ D v w = 0 := by
    change tauZ.symm (E (eP v) (eZ w)) = 0 ↔ D v w = 0
    exact (tauZ.symm.map_eq_zero_iff).trans (hzero v w)
  obtain ⟨_, _, _, hfield⟩ := CFSGSesquilinearKernelRigidity.common_scalar_and_field
    sigma ((tauP.trans sigma).trans tauZ.symm) D (pulledCrossDual tauP tauZ E eP eZ)
    hD (pulledCrossDual_smul sigma tauP tauZ E hE eP eZ) hker i₀ i₁ hne
  apply RingEquiv.ext
  intro a
  apply sigma.injective
  have hh := congrArg (fun rho : K ≃+* K => tauZ (rho a)) hfield
  change tauZ (sigma a) = tauZ (tauZ.symm (sigma (tauP a))) at hh
  exact (tauZ.apply_symm_apply _).symm.trans (hh.symm.trans (hcomm a).symm)

end SymmetricSubgroupAsymptotics.CFSGSesquilinearOpposedFieldCoherence
