import SymmetricSubgroupAsymptotics.GeneralThreeTwoMatrixEncoding
import Mathlib.Data.Fin.VecNotation

/-! Faithful action of the actual GL3(2) on the eight binary vectors, with
an explicit binary point chart. This will bind selected matrix subgroups
to the already fixed literal small-affine complement representatives. -/

set_option autoImplicit false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.GeneralThreeTwoPointAction

abbrev Vector := Fin 3 → ZMod 2
abbrev Ambient := GeneralThreeTwoMatrixEncoding.Ambient

def points : Vector ≃ Fin 8 where
  toFun v := finFunctionFinEquiv (fun i => (ZMod.finEquiv 2).symm (v i))
  invFun x := fun i => ZMod.finEquiv 2 (finFunctionFinEquiv.symm x i)
  left_inv v := by ext i; simp
  right_inv x := by simp

private def vectorPerm : Ambient →* Equiv.Perm Vector where
  toFun g := (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv.toEquiv
  map_one' := by
    rw [map_one]
    rfl
  map_mul' g h := by
    rw [map_mul]
    rfl

def action : Ambient →* Equiv.Perm (Fin 8) :=
  points.permCongrHom.toMonoidHom.comp vectorPerm

theorem action_apply (g : Ambient) (x : Fin 8) :
    action g x = points (g.val *ᵥ points.symm x) := rfl

theorem action_injective : Function.Injective action := by
  intro g h he
  change points.permCongrHom (vectorPerm g) = points.permCongrHom (vectorPerm h) at he
  have hvec := points.permCongrHom.injective he
  apply Matrix.GeneralLinearGroup.toLin.injective
  apply Units.ext
  apply LinearMap.ext
  intro v
  exact Equiv.congr_fun hvec v

end SymmetricSubgroupAsymptotics.GeneralThreeTwoPointAction

end
