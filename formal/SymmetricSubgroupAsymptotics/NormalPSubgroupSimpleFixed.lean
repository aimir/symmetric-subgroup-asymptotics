import SymmetricSubgroupAsymptotics.SchurPGroupCapacity

/-! A normal defining-characteristic p-subgroup fixes every vector in a
finite simple representation of the original whole group. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

/-- The nonzero p-subgroup fixed space is invariant under the original
whole group by normality, so simplicity makes it the whole module. -/
theorem normal_pSubgroup_simple_representation_fixed
    {p : ℕ} [Fact p.Prime] {G V : Type} [Group G]
    [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (rho : Representation (ZMod p) G V)
    [IsSimpleModule (ZMod p)[G] rho.asModule]
    (P : Subgroup G) [P.Normal] (hP : IsPGroup p P) :
    ∀ (g : P) (v : V), rho g v = v := by
  letI : Nontrivial rho.asModule := IsSimpleModule.nontrivial (ZMod p)[G] rho.asModule
  letI : Nontrivial V := rho.asModuleEquiv.toEquiv.symm.nontrivial
  obtain ⟨v, hv, hfixed⟩ := pGroup_representation_nonzero_fixed hP (rho.comp P.subtype)
  let F : Subrepresentation rho :=
    ⟨Representation.invariants (rho.comp P.subtype), Representation.le_comap_invariants rho P⟩
  have htop : F.asSubmodule = ⊤ := by
    apply (eq_bot_or_eq_top F.asSubmodule).resolve_left
    intro hbot
    have hvF : rho.asModuleEquiv.symm v ∈ F.asSubmodule := by
      change ∀ g : P, rho g v = v
      exact hfixed
    rw [hbot] at hvF
    have hz : rho.asModuleEquiv.symm v = 0 := hvF
    exact hv (by simpa using congrArg rho.asModuleEquiv hz)
  intro g w
  have hw : rho.asModuleEquiv.symm w ∈ F.asSubmodule := by
    rw [htop]
    trivial
  change ∀ h : P, rho h w = w at hw
  exact hw g

end SymmetricSubgroupAsymptotics

end
