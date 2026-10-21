import Mathlib.RepresentationTheory.Basic

/-! An actual group difference is a literal group-algebra operator.
Keeping the representation as a parameter avoids unfolding any concrete
subrepresentation or permutation action. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics
variable {k G M : Type} [Field k] [Group G] [AddCommGroup M] [Module k M]

theorem representation_difference_operator
    (rho : Representation k G M) (g : G) (v : rho.asModule) :
    rho.asModuleEquiv ((MonoidAlgebra.single g (1 : k)-1) • v)=
      rho g (rho.asModuleEquiv v)-rho.asModuleEquiv v := by
  rw [sub_smul,Representation.single_smul,one_smul,one_smul,map_sub]
  rfl

end SymmetricSubgroupAsymptotics
