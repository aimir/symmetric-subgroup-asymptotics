import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.TypeTags.Hom

/-! Exact transport between automorphisms of an additive group and of
its multiplicative type tag, with the same underlying elements. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGAdditiveAutomorphismTransport
variable (A : Type*) [AddGroup A]

def multiplicativeAddAutEquiv : MulAut (Multiplicative A) ≃* AddAut A where
  toFun f :=
    { toFun x := (f (Multiplicative.ofAdd x)).toAdd
      invFun x := (f.symm (Multiplicative.ofAdd x)).toAdd
      left_inv x := f.symm_apply_apply (Multiplicative.ofAdd x)
      right_inv x := f.apply_symm_apply (Multiplicative.ofAdd x)
      map_add' x y := map_mul f (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) }
  invFun f :=
    { toFun x := Multiplicative.ofAdd (f x.toAdd)
      invFun x := Multiplicative.ofAdd (f.symm x.toAdd)
      left_inv x := congrArg Multiplicative.ofAdd (f.symm_apply_apply x.toAdd)
      right_inv x := congrArg Multiplicative.ofAdd (f.apply_symm_apply x.toAdd)
      map_mul' x y := congrArg Multiplicative.ofAdd (map_add f x.toAdd y.toAdd) }
  left_inv f := by apply MulEquiv.ext;intro x;rfl
  right_inv f := by apply AddEquiv.ext;intro x;rfl
  map_mul' f g := by apply AddEquiv.ext;intro x;rfl

end SymmetricSubgroupAsymptotics.CFSGAdditiveAutomorphismTransport
