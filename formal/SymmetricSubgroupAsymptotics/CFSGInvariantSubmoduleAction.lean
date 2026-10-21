import SymmetricSubgroupAsymptotics.CFSGInvariantQuotientAction

/-! The actual two-sided submodule stabilizer acts on the submodule
itself. This complements its already checked quotient action. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGInvariantSubmoduleAction
open CFSGInvariantQuotientAction
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

def restrictionEquiv (S : Submodule R M) (g : stabilizer S) : S ≃ₗ[R] S where
  __ := g.val.toLinearMap.restrict g.property.1
  invFun x := ⟨g.val.symm x.val, g.property.2 x.val x.property⟩
  left_inv x := Subtype.ext (g.val.symm_apply_apply x.val)
  right_inv x := Subtype.ext (g.val.apply_symm_apply x.val)

@[simp] theorem restrictionEquiv_apply (S : Submodule R M) (g : stabilizer S) (x : S) :
    (restrictionEquiv S g x).val = g.val x.val := rfl

def restrictionAction (S : Submodule R M) : stabilizer S →* (S ≃ₗ[R] S) where
  toFun := restrictionEquiv S
  map_one' := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    rfl
  map_mul' := by
    intro g h
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    rfl

end SymmetricSubgroupAsymptotics.CFSGInvariantSubmoduleAction
