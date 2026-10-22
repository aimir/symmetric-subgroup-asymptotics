import SymmetricSubgroupAsymptotics.CliffordRestriction
import Mathlib.Algebra.Group.Subgroup.Lattice

/-! A normal subgroup supplemented by its centralizer has homogeneous
restriction on an irreducible module. Fully invariant submodules of the
restriction are invariant under both supplement factors, hence under the
whole actual group. This applies to each factor of an actual direct product. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.CFSGCentralizerSupplementIsotypic

variable {k G V : Type} [Field k] [Group G] [Finite G]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]

abbrev restriction (rho : Representation k G V) (H : Subgroup G) : Representation k H V :=
  rho.comp H.subtype

theorem restriction_isotypic_of_centralizer_supplement
    (rho : Representation k G V) (hrho : Representation.IsIrreducible rho)
    (H : Subgroup G) [H.Normal]
    (hsup : H ⊔ Subgroup.centralizer (H : Set G) = ⊤) :
    IsIsotypic k[H] (restriction rho H).asModule := by
  let tau : Representation k H V := rho.comp H.subtype
  letI : Representation.IsIrreducible rho := hrho
  letI : IsSemisimpleModule k[H] tau.asModule :=
    CliffordRawRestriction.proved.semisimple rho hrho H
  apply isIsotypic_iff_isFullyInvariant_imp_bot_or_top.mpr
  intro m hm
  let U0 : Subrepresentation tau := Subrepresentation.ofSubmodule' m
  have hcentral (c : G) (hc : c ∈ Subgroup.centralizer (H : Set G))
      (v : V) (hv : v ∈ U0.toSubmodule) : rho c v ∈ U0.toSubmodule := by
    let f : tau.IntertwiningMap tau :=
      (rho c).intertwiningMap_of_isIntertwiningMap tau tau (fun h x => by
        have he : c * (h : G) = (h : G) * c :=
          ((Subgroup.mem_centralizer_iff.mp hc) h h.property).symm
        have hh := congrArg (fun a : G => rho a x) he
        simpa only [map_mul, Module.End.mul_apply] using hh)
    let F : Module.End k[H] tau.asModule :=
      Representation.IntertwiningMap.equivLinearMapAsModule tau tau f
    have hh := hm F hv
    exact hh
  let U : Subrepresentation rho := {
    toSubmodule := U0.toSubmodule
    apply_mem_toSubmodule := by
      intro g v hv
      have hg : g ∈ H ⊔ Subgroup.centralizer (H : Set G) := by rw [hsup]; trivial
      obtain ⟨h, hh, c, hc, he⟩ := Subgroup.mem_sup_of_normal_left.mp hg
      rw [← he, map_mul, Module.End.mul_apply]
      exact U0.apply_mem_toSubmodule ⟨h, hh⟩ (hcentral c hc v hv) }
  rcases eq_bot_or_eq_top U with hU | hU
  · apply Or.inl
    apply bot_unique
    intro x hx
    change x = 0
    have hv : tau.asModuleEquiv x ∈ U.toSubmodule := hx
    rw [hU] at hv
    change tau.asModuleEquiv x = 0 at hv
    exact tau.asModuleEquiv.injective (hv.trans (map_zero tau.asModuleEquiv).symm)
  · apply Or.inr
    apply top_unique
    intro x _
    have hv : tau.asModuleEquiv x ∈ U.toSubmodule := by rw [hU]; trivial
    exact hv

end SymmetricSubgroupAsymptotics.CFSGCentralizerSupplementIsotypic
