import SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoCongruence
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Pi

/-! Undoing the auxiliary GL2 congruence on Hermitian coefficients
undoes the SAME coordinate change on the semilinear vector map. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
variable {K : Type*} [Field K]

theorem undo_congruence_rankOne (sigma theta : K ≃+* K)
    (hsigma : ∀ x, sigma (sigma x) = x) (E : parameters sigma ≃+ parameters sigma)
    (D : (Matrix (Fin 2) (Fin 2) K)ˣ)
    (L : (Fin 2 → K) →ₛₗ[theta.toRingHom] (Fin 2 → K))
    (hL : Function.Injective L) (c : K) (hc : sigma c = c)
    (hR : ∀ v, (E.trans (coefficientCongruence sigma hsigma D))
      (rankOneParameter sigma hsigma 1 (map_one sigma) v) =
        rankOneParameter sigma hsigma c hc (L v)) :
    ∃ M : (Fin 2 → K) →ₛₗ[theta.toRingHom] (Fin 2 → K),
      Function.Injective M ∧ ∀ v,
        E (rankOneParameter sigma hsigma 1 (map_one sigma) v) =
          rankOneParameter sigma hsigma c hc (M v) := by
  let M := (Matrix.mulVecLin (D⁻¹).val).comp L
  have hD : Function.Injective (Matrix.mulVecLin (D⁻¹).val) :=
    Matrix.mulVec_injective_iff_isUnit.mpr (D⁻¹).isUnit
  refine ⟨M, hD.comp hL, ?_⟩
  intro v
  have hh := congrArg (coefficientCongruence sigma hsigma D).symm (hR v)
  change (coefficientCongruence sigma hsigma D).symm
    (coefficientCongruence sigma hsigma D (E (rankOneParameter sigma hsigma 1 (map_one sigma) v))) = _ at hh
  rw [AddEquiv.symm_apply_apply] at hh
  change E (rankOneParameter sigma hsigma 1 (map_one sigma) v) =
    coefficientCongruence sigma hsigma D⁻¹ (rankOneParameter sigma hsigma c hc (L v)) at hh
  rw [coefficientCongruence_rankOne] at hh
  exact hh

end SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
