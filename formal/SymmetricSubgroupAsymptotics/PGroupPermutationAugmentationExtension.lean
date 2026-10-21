import SymmetricSubgroupAsymptotics.PGroupPermutationAugmentationInterval

/-! Install an actual invariant extension A<T inside the original
augmentation, with every displacement of T already in A. Only this one
interval is extended; no splitting of a group or module is asserted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]

theorem invariant_span_fixed_lift_displacement
    (rho : Representation k G V) (A : Subrepresentation rho) (v : V)
    (hv : ∀ g,rho g v-v ∈ A.toSubmodule)
    (g : G) : A.toSubmodule ⊔ Submodule.span k {v} ≤
      A.toSubmodule.comap ((rho g : V →ₗ[k] V)-LinearMap.id) := by
  apply sup_le
  · intro a ha
    exact A.toSubmodule.sub_mem (A.apply_mem_toSubmodule g ha) ha
  · apply Submodule.span_le.mpr
    intro a ha
    have he : a=v := Set.mem_singleton_iff.mp ha
    subst a
    exact hv g

def invariantSpanFixedLift
    (rho : Representation k G V) (A : Subrepresentation rho) (v : V)
    (hv : ∀ g,rho g v-v ∈ A.toSubmodule) : Subrepresentation rho where
  toSubmodule := A.toSubmodule ⊔ Submodule.span k {v}
  apply_mem_toSubmodule g a ha := by
    have hd := invariant_span_fixed_lift_displacement rho A v hv g ha
    have hs : rho g a-a ∈ A.toSubmodule ⊔ Submodule.span k {v} :=
      (show A.toSubmodule ≤ A.toSubmodule ⊔ Submodule.span k {v} from le_sup_left) hd
    simpa only [sub_add_cancel] using
      (A.toSubmodule ⊔ Submodule.span k {v}).add_mem hs ha

theorem invariantSpanFixedLift_displacement
    (rho : Representation k G V) (A : Subrepresentation rho) (v : V)
    (hv : ∀ g,rho g v-v ∈ A.toSubmodule)
    (g : G) (a : V) (ha : a∈(invariantSpanFixedLift rho A v hv).toSubmodule) :
    rho g a-a∈A.toSubmodule :=
  invariant_span_fixed_lift_displacement rho A v hv g ha

theorem invariantSpanFixedLift_strict
    (rho : Representation k G V) (A : Subrepresentation rho) (v : V)
    (hv : ∀ g,rho g v-v ∈ A.toSubmodule) (hnot : v∉A.toSubmodule) :
    A.toSubmodule < (invariantSpanFixedLift rho A v hv).toSubmodule := by
  apply lt_of_le_of_ne le_sup_left
  intro he
  apply hnot
  rw [he]
  exact (show Submodule.span k {v} ≤ A.toSubmodule ⊔ Submodule.span k {v} from le_sup_right)
    (Submodule.subset_span (Set.mem_singleton v))

theorem pGroup_exists_augmentation_trivial_interval
    {p : ℕ} [Fact p.Prime] {X : Type} [MulAction G X] [Finite X]
    [MulAction.IsPretransitive G X]
    (hG : IsPGroup p G)
    (A : Subrepresentation (permutationFunctionRepresentation (ZMod p) G X))
    (hA : A.toSubmodule < PermutationAugmentation.space (ZMod p) X) :
    ∃ T : Subrepresentation (permutationFunctionRepresentation (ZMod p) G X),
      A.toSubmodule < T.toSubmodule ∧
      T.toSubmodule ≤ PermutationAugmentation.space (ZMod p) X ∧
      ∀ (g : G) (a : X → ZMod p),a∈T.toSubmodule →
        permutationFunctionRepresentation (ZMod p) G X g a-a∈A.toSubmodule := by
  obtain ⟨v,hv,hnot,hdisp⟩ := pGroup_augmentation_interval_fixed_lift hG A hA
  refine ⟨invariantSpanFixedLift _ A v hdisp,
    invariantSpanFixedLift_strict _ A v hdisp hnot,?_,?_⟩
  · exact sup_le hA.le (Submodule.span_le.mpr (by
      intro a ha
      rcases Set.mem_singleton_iff.mp ha with rfl
      exact hv))
  · exact invariantSpanFixedLift_displacement _ A v hdisp

end SymmetricSubgroupAsymptotics
