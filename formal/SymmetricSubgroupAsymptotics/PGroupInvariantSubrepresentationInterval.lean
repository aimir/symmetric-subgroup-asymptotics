import SymmetricSubgroupAsymptotics.PGroupPermutationAugmentationExtension

/-! A trivial one-dimensional interval is selected inside an arbitrary
actual invariant interval A<S. The ambient action and both endpoints
are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {p : ℕ} [Fact p.Prime] {G V : Type} [Group G]
    [AddCommGroup V] [Module (ZMod p) V] [Finite V]

theorem pGroup_exists_trivial_subrepresentation_interval
    (hG : IsPGroup p G) (rho : Representation (ZMod p) G V)
    (A S : Subrepresentation rho) (hAS : A.toSubmodule<S.toSubmodule) :
    ∃ T : Subrepresentation rho,A.toSubmodule<T.toSubmodule ∧
      T.toSubmodule≤S.toSubmodule ∧
      ∀ (g : G) (v : V),v∈T.toSubmodule → rho g v-v∈A.toSubmodule := by
  let D := nestedSubrepresentation A S hAS.le
  have hproper : D.toSubmodule ≠ ⊤ := by
    intro he
    obtain ⟨v,hv,hnot⟩ := SetLike.exists_of_lt hAS
    have hm : (⟨v,hv⟩ : S.toSubmodule) ∈ D.toSubmodule := by
      rw [he]
      exact Submodule.mem_top
    exact hnot hm
  obtain ⟨v,hv,hfixed⟩ := pGroup_invariant_interval_fixed_lift hG S.toRepresentation D hproper
  have hnot : v.val∉A.toSubmodule := hv
  have hdisp : ∀ g,rho g v.val-v.val∈A.toSubmodule := hfixed
  refine ⟨invariantSpanFixedLift rho A v.val hdisp,
    invariantSpanFixedLift_strict rho A v.val hdisp hnot,?_,?_⟩
  · exact sup_le hAS.le (Submodule.span_le.mpr (by
      intro a ha
      rcases Set.mem_singleton_iff.mp ha with rfl
      exact v.property))
  · exact invariantSpanFixedLift_displacement rho A v.val hdisp

end SymmetricSubgroupAsymptotics
