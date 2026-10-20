import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! Actual automorphisms of an elementary abelian group are linear in
every specified ZMod coordinate chart. The equivalence retains the pointwise
action, rather than just identifying the abstract automorphism groups. -/

set_option autoImplicit false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.ElementaryZModAutomorphismCoordinates

variable (p : ℕ) (V : Type*) [AddCommGroup V] [Module (ZMod p) V]

def linearEquiv : MulAut (Multiplicative V) ≃* (V ≃ₗ[ZMod p] V) where
  toFun e := (AddEquiv.toMultiplicative.symm e).toLinearEquiv
    (fun c x => ZMod.map_smul (AddEquiv.toMultiplicative.symm e) c x)
  invFun e := e.toAddEquiv.toMultiplicative
  left_inv e := by
    apply MulEquiv.ext
    intro v
    rfl
  right_inv e := by
    apply LinearEquiv.ext
    intro v
    rfl
  map_mul' e f := by
    apply LinearEquiv.ext
    intro v
    rfl

/-- The actual matrix group, with the same coordinates on vectors. -/
def matrixEquiv (n : ℕ) :
    MulAut (Multiplicative (Fin n → ZMod p)) ≃*
      Matrix.GeneralLinearGroup (Fin n) (ZMod p) :=
  (linearEquiv p (Fin n → ZMod p)).trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv
      (ZMod p) (Fin n → ZMod p)).symm.trans Matrix.GeneralLinearGroup.toLin.symm)

theorem matrixEquiv_apply (n : ℕ)
    (e : MulAut (Multiplicative (Fin n → ZMod p))) (v : Fin n → ZMod p) :
    (matrixEquiv p n e).val *ᵥ v =
      (e (Multiplicative.ofAdd v)).toAdd := by
  change (Matrix.GeneralLinearGroup.toLin
    (Matrix.GeneralLinearGroup.toLin.symm
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv
        (ZMod p) (Fin n → ZMod p)).symm (linearEquiv p _ e)))).toLinearEquiv v = _
  rw [MulEquiv.apply_symm_apply]
  rfl

end SymmetricSubgroupAsymptotics.ElementaryZModAutomorphismCoordinates

end
