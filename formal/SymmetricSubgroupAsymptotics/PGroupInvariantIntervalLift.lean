import SymmetricSubgroupAsymptotics.SchurPGroupCapacity

/-! A nonzero interval of an actual defining-characteristic representation
contains a one-dimensional trivial subrepresentation. The lift belongs to
the original vector space and all displacements lie in the SAME denominator. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {p : ℕ} [Fact p.Prime] {G V : Type} [Group G]
    [AddCommGroup V] [Module (ZMod p) V] [Finite V]

theorem pGroup_invariant_interval_fixed_lift
    (hG : IsPGroup p G) (rho : Representation (ZMod p) G V)
    (S : Subrepresentation rho) (hproper : S.toSubmodule ≠ ⊤) :
    ∃ v : V, v ∉ S.toSubmodule ∧ ∀ g : G, rho g v-v ∈ S.toSubmodule := by
  let sigma := rho.quotient S.toSubmodule
    (fun g v hv => S.apply_mem_toSubmodule g hv)
  letI : Finite (V ⧸ S.toSubmodule) :=
    Finite.of_surjective S.toSubmodule.mkQ S.toSubmodule.mkQ_surjective
  obtain ⟨v,hv⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hproper)
  letI : Nontrivial (V ⧸ S.toSubmodule) :=
    ⟨⟨S.toSubmodule.mkQ v,0,by
      intro he
      exact hv.2 ((Submodule.Quotient.mk_eq_zero S.toSubmodule).mp he)⟩⟩
  obtain ⟨a,ha,hfixed⟩ := pGroup_representation_nonzero_fixed hG sigma
  obtain ⟨v,rfl⟩ := S.toSubmodule.mkQ_surjective a
  refine ⟨v,?_,?_⟩
  · intro hv
    exact ha ((Submodule.Quotient.mk_eq_zero S.toSubmodule).mpr hv)
  · intro g
    apply (Submodule.Quotient.mk_eq_zero S.toSubmodule).mp
    change S.toSubmodule.mkQ (rho g v-v)=0
    rw [map_sub]
    have he := hfixed g
    change S.toSubmodule.mkQ (rho g v)=S.toSubmodule.mkQ v at he
    rw [he,sub_self]

end SymmetricSubgroupAsymptotics
