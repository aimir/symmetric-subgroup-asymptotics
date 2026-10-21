import SymmetricSubgroupAsymptotics.GeneralFourTwoMatrixEncoding

/-! The actual four-dimensional matrix action, its linear equivalence,
and the sixteen physical binary points. Conjugators stay actual linear
maps; an abstract subgroup isomorphism is never treated as a point chart. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.GeneralFourTwoPointAction

abbrev Vector := Fin 4 → ZMod 2
abbrev Ambient := GeneralFourTwoMatrixEncoding.Ambient
abbrev LinearGroup := Vector ≃ₗ[ZMod 2] Vector

def linearEquiv : Ambient ≃* LinearGroup :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Vector)

theorem linearEquiv_apply (g : Ambient) (v : Vector) :
    linearEquiv g v = g.val *ᵥ v := rfl

def points : Vector ≃ Fin 16 where
  toFun v := finFunctionFinEquiv (fun i => (ZMod.finEquiv 2).symm (v i))
  invFun x := fun i => ZMod.finEquiv 2 (finFunctionFinEquiv.symm x i)
  left_inv v := by ext i; simp
  right_inv x := by simp

private def vectorPerm : Ambient →* Equiv.Perm Vector where
  toFun g := (linearEquiv g).toEquiv
  map_one' := by rw [map_one]; rfl
  map_mul' g h := by rw [map_mul]; rfl

def action : Ambient →* Equiv.Perm (Fin 16) :=
  points.permCongrHom.toMonoidHom.comp vectorPerm

theorem action_apply (g : Ambient) (x : Fin 16) :
    action g x = points (g.val *ᵥ points.symm x) := rfl

theorem action_injective : Function.Injective action := by
  intro g h he
  change points.permCongrHom (vectorPerm g) = points.permCongrHom (vectorPerm h) at he
  have hvec := points.permCongrHom.injective he
  apply linearEquiv.injective
  apply LinearEquiv.ext
  intro v
  exact Equiv.congr_fun hvec v

end SymmetricSubgroupAsymptotics.GeneralFourTwoPointAction
