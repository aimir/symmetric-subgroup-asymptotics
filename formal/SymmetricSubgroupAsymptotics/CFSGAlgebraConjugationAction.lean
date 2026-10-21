import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Algebra.Basic

/-! Literal conjugation by algebra units, as an actual linear group
homomorphism. This is independent of a source presentation. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGAlgebraConjugationAction
variable (R B : Type*) [CommRing R] [Ring B] [Algebra R B]

def action : Bˣ →* (B ≃ₗ[R] B) where
  toFun u := (Units.mulLeftLinearEquiv R B u).trans (Units.mulRightLinearEquiv R u⁻¹)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    change (1 : B) * x * 1 = x
    simp only [one_mul, mul_one]
  map_mul' := by
    intro u v
    apply LinearEquiv.ext
    intro x
    change ((u * v : Bˣ) : B) * x * ↑((u * v)⁻¹) =
      (u : B) * ((v : B) * x * ↑(v⁻¹)) * ↑(u⁻¹)
    simp only [Units.val_mul, mul_inv_rev, mul_assoc]

@[simp] theorem action_apply (u : Bˣ) (x : B) :
    action R B u x = (u : B) * x * ↑(u⁻¹) := rfl

end SymmetricSubgroupAsymptotics.CFSGAlgebraConjugationAction
