import SymmetricSubgroupAsymptotics.CFSGProjectiveFrameCoordinates
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Projectivization.Action

/-! Explicit linear normalization of a projective frame. A final point
with every basis coordinate nonzero determines the column scalings;
the resulting invertible linear map sends the coordinate frame to the
given literal basis lines and final point. -/
set_option autoImplicit false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveFrameNormalization
variable {F n V : Type*} [Field F] [Fintype n] [DecidableEq n]
  [AddCommGroup V] [Module F V]

theorem exists_normalized_linearEquiv (B : Module.Basis n F V) (w : V)
    (hw : ∀ i, B.repr w i ≠ 0) :
    ∃ a : (n → F) ≃ₗ[F] V,
      (∀ i, a (Pi.single i 1) = (B.repr w i) • B i) ∧ a (fun _ => 1) = w := by
  let B' := B.unitsSMul (fun i => Units.mk0 (B.repr w i) (hw i))
  refine ⟨B'.equivFun.symm, ?_, ?_⟩
  · intro i
    simp [Module.Basis.equivFun_symm_apply, B', Module.Basis.unitsSMul_apply,
      Units.smul_def]
  · rw [Module.Basis.equivFun_symm_apply]
    simp only [one_smul]
    simpa only [B', Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0]
      using B.sum_repr w

end SymmetricSubgroupAsymptotics.CFSGProjectiveFrameNormalization
