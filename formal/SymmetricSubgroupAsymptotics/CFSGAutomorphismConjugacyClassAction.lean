import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.GroupTheory.GroupAction.Quotient

/-! Automorphisms act on the actual conjugacy classes of a group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGAutomorphismConjugacyClassAction
variable (G : Type*) [Group G]

instance cfsgAutomorphismConjugacyClassAction : MulAction (MulAut G) (ConjClasses G) where
  smul f c := ConjClasses.map f.toMonoidHom c
  one_smul c := by
    obtain ⟨g,rfl⟩ := ConjClasses.mk_surjective c
    rfl
  mul_smul f h c := by
    obtain ⟨g,rfl⟩ := ConjClasses.mk_surjective c
    rfl

@[simp] theorem smul_mk (f : MulAut G) (g : G) :
    f • ConjClasses.mk g=ConjClasses.mk (f g) := rfl

end SymmetricSubgroupAsymptotics.CFSGAutomorphismConjugacyClassAction
