import SymmetricSubgroupAsymptotics.CFSGSesquilinearKernelRigidity
import SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
import SymmetricSubgroupAsymptotics.CFSGHermitianMaximalExchange
import Mathlib.LinearAlgebra.Pi

/-! Cross-pairing field coherence for two semilinear EMBEDDINGS into
the ambient Hermitian space. No target-space surjectivity or target
duality is required: only the original nondegenerate cross-duality and
the SAME actual zero-pairing tests are used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGHermitianCrossEmbeddingFieldCoherence
open CFSGTwistedAUnitaryParameters CFSGHermitianOrthogonalSpan
variable {K I J : Type*} [Field K] [Fintype I] [DecidableEq I] [Fintype J]

def pulledPair (sigma tauP tauZ : K ≃+* K) (H : Matrix J J K)
    (a : (I → K) →ₛₗ[tauP.toRingHom] (J → K))
    (b : (I → K) →ₛₗ[tauZ.toRingHom] (J → K)) :
    (I → K) →+ Module.Dual K (I → K) where
  toFun v := {
    toFun := fun w => tauZ.symm (pairRightLinear sigma H (a v) (b w))
    map_add' := by intro w z; simp only [map_add]
    map_smul' := by
      intro c w
      change tauZ.symm (pairRightLinear sigma H (a v) (b (c • w))) =
        c * tauZ.symm (pairRightLinear sigma H (a v) (b w))
      rw [map_smulₛₗ, map_smul]
      change tauZ.symm (tauZ c * pairRightLinear sigma H (a v) (b w)) = _
      rw [map_mul, tauZ.symm_apply_apply] }
  map_zero' := by
    apply LinearMap.ext
    intro w
    change tauZ.symm (hermitianPair sigma H (a 0) (b w)) = 0
    rw [map_zero]
    simp [hermitianPair, Function.comp_def]
  map_add' v z := by
    apply LinearMap.ext
    intro w
    change tauZ.symm (hermitianPair sigma H (a (v + z)) (b w)) =
      tauZ.symm (hermitianPair sigma H (a v) (b w)) +
        tauZ.symm (hermitianPair sigma H (a z) (b w))
    rw [map_add, hermitianPair_add_left, map_add]

theorem pulledPair_smul (sigma tauP tauZ : K ≃+* K) (H : Matrix J J K)
    (a : (I → K) →ₛₗ[tauP.toRingHom] (J → K))
    (b : (I → K) →ₛₗ[tauZ.toRingHom] (J → K)) (c : K) (v : I → K) :
    pulledPair sigma tauP tauZ H a b (c • v) =
      ((tauP.trans sigma).trans tauZ.symm) c • pulledPair sigma tauP tauZ H a b v := by
  apply LinearMap.ext
  intro w
  change tauZ.symm (hermitianPair sigma H (a (c • v)) (b w)) =
    tauZ.symm (sigma (tauP c)) * tauZ.symm (hermitianPair sigma H (a v) (b w))
  rw [map_smulₛₗ]
  change tauZ.symm (hermitianPair sigma H ((tauP c) • a v) (b w)) =
    tauZ.symm (sigma (tauP c)) * tauZ.symm (hermitianPair sigma H (a v) (b w))
  have hh := hermitianPair_smul sigma H (tauP c) 1 (a v) (b w)
  simp only [one_smul, mul_one] at hh
  rw [hh, map_mul]

theorem fields_eq_of_cross_zero_iff (sigma tauP tauZ : K ≃+* K) (H : Matrix J J K)
    (D : (I → K) ≃+ Module.Dual K (I → K))
    (hD : ∀ (c : K) (v : I → K), D (c • v) = sigma c • D v)
    (a : (I → K) →ₛₗ[tauP.toRingHom] (J → K))
    (b : (I → K) →ₛₗ[tauZ.toRingHom] (J → K))
    (hzero : ∀ v w, hermitianPair sigma H (a v) (b w) = 0 ↔ D v w = 0)
    (hcomm : Function.Commute sigma tauZ) (i₀ i₁ : I) (hne : i₀ ≠ i₁) : tauP = tauZ := by
  have hker (v w : I → K) : pulledPair sigma tauP tauZ H a b v w = 0 ↔ D v w = 0 := by
    change tauZ.symm (hermitianPair sigma H (a v) (b w)) = 0 ↔ D v w = 0
    exact (tauZ.symm.map_eq_zero_iff).trans (hzero v w)
  obtain ⟨_, _, _, hfield⟩ := CFSGSesquilinearKernelRigidity.common_scalar_and_field
    sigma ((tauP.trans sigma).trans tauZ.symm) D (pulledPair sigma tauP tauZ H a b)
    hD (pulledPair_smul sigma tauP tauZ H a b) hker i₀ i₁ hne
  apply RingEquiv.ext
  intro c
  apply sigma.injective
  have hh := congrArg (fun rho : K ≃+* K => tauZ (rho c)) hfield
  change tauZ (sigma c) = tauZ (tauZ.symm (sigma (tauP c))) at hh
  exact (tauZ.apply_symm_apply _).symm.trans (hh.symm.trans (hcomm c).symm)

end SymmetricSubgroupAsymptotics.CFSGHermitianCrossEmbeddingFieldCoherence
