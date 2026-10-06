import SymmetricSubgroupAsymptotics.PermutationalWreathProduct
import Mathlib.RepresentationTheory.Basic

/-!
# The linear function representation of a permutational wreath product

The base group acts coordinatewise and the top group permutes coordinates.
This is the full induced frame in which the correlated translation module
of an imprimitive affine action embeds.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PermutationalWreathProduct

variable {k D Q I V : Type*} [Field k] [Group D] [Group Q]
  [MulAction Q I] [AddCommGroup V] [Module k V]

/-- The natural monomial action on `I → V`.  With the wreath convention
used in this project, the value at `i` is first pulled back along the inverse
top motion and then acted on by the base coordinate at `i`. -/
def functionRepresentation (rho : Representation k D V) :
    Representation k (PermutationalWreathProduct D Q I) (I → V) where
  toFun w := {
    toFun := fun f i ↦ rho (w.left i) (f (w.right⁻¹ • i))
    map_add' := by intro f g; funext i; exact map_add _ _ _
    map_smul' := by intro c f; funext i; exact map_smul _ _ _ }
  map_one' := by
    apply LinearMap.ext
    intro f
    funext i
    simp only [one_left, Pi.one_apply, one_right, inv_one, one_smul,
      map_one, Module.End.one_apply]
    rfl
  map_mul' a b := by
    apply LinearMap.ext
    intro f
    funext i
    change rho ((a * b).left i) (f ((a * b).right⁻¹ • i)) =
      rho (a.left i)
        (rho (b.left (a.right⁻¹ • i))
          (f (b.right⁻¹ • (a.right⁻¹ • i))))
    rw [mul_left, mul_right, Pi.mul_apply, map_mul]
    simp only [mul_inv_rev, mul_smul, Module.End.mul_apply]

@[simp]
theorem functionRepresentation_apply (rho : Representation k D V)
    (w : PermutationalWreathProduct D Q I) (f : I → V) (i : I) :
    functionRepresentation (Q := Q) (I := I) rho w f i =
      rho (w.left i) (f (w.right⁻¹ • i)) := rfl

end PermutationalWreathProduct
end SymmetricSubgroupAsymptotics

end
