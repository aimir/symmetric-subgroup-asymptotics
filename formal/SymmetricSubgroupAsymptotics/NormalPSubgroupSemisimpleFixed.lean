import SymmetricSubgroupAsymptotics.NormalPSubgroupSimpleFixed
import SymmetricSubgroupAsymptotics.RepresentationCoordinateHeads

/-! A normal defining-characteristic p-subgroup fixes the actual entire
semisimple target, not only a chosen simple constituent. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

theorem normal_pSubgroup_semisimple_representation_fixed
    {p : ℕ} [Fact p.Prime] {G V : Type} [Group G]
    [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (rho : Representation (ZMod p) G V)
    [IsSemisimpleModule (ZMod p)[G] rho.asModule]
    (P : Subgroup G) [P.Normal] (hP : IsPGroup p P) :
    ∀ (g : P) (v : V), rho g v = v := by
  let F : Subrepresentation rho :=
    ⟨Representation.invariants (rho.comp P.subtype), Representation.le_comap_invariants rho P⟩
  have htop : F.asSubmodule = ⊤ := by
    apply top_unique
    rw [← IsSemisimpleModule.sSup_simples_eq_top (ZMod p)[G] rho.asModule]
    apply sSup_le
    intro S hS
    letI : IsSimpleModule (ZMod p)[G] S := hS
    let T : Subrepresentation rho := Subrepresentation.ofSubmodule' S
    letI : IsSimpleModule (ZMod p)[G] T.toRepresentation.asModule :=
      (submoduleRepresentationModuleEquiv rho S).isSimpleModule_iff.mp inferInstance
    intro v hv
    change ∀ g : P, rho g (rho.asModuleEquiv v) = rho.asModuleEquiv v
    intro g
    let x : T.toSubmodule := ⟨rho.asModuleEquiv v, hv⟩
    have hx := normal_pSubgroup_simple_representation_fixed T.toRepresentation P hP g x
    exact congrArg Subtype.val hx
  intro g v
  have hv : rho.asModuleEquiv.symm v ∈ F.asSubmodule := by
    rw [htop]
    trivial
  change ∀ h : P, rho h v = v at hv
  exact hv g

end SymmetricSubgroupAsymptotics

end
