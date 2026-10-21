import SymmetricSubgroupAsymptotics.PGroupInvariantIntervalLift
import SymmetricSubgroupAsymptotics.PGroupPermutationPointwiseAnnihilator
import SymmetricSubgroupAsymptotics.PermutationFunctionSelfDual
import SymmetricSubgroupAsymptotics.RepresentationSelfDualNestedQuotient
import SymmetricSubgroupAsymptotics.PermutationBinaryFourAugmentation

/-! Proper submodules of an original transitive defining-characteristic
permutation module lie in its literal sum-zero hyperplane. Inside that
hyperplane every proper invariant denominator has an actual fixed lift.
These statements require no registry of invariant subspaces. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics

variable {p : ℕ} [Fact p.Prime] {G X : Type} [Group G]
    [MulAction G X] [Finite X] [MulAction.IsPretransitive G X]

theorem pGroup_permutation_proper_subrepresentation_le_augmentation
    (hG : IsPGroup p G) (x : X)
    (A : Subrepresentation (permutationFunctionRepresentation (ZMod p) G X))
    (hproper : A.toSubmodule ≠ ⊤) :
    A.toSubmodule ≤ PermutationAugmentation.space (ZMod p) X := by
  let rho := permutationFunctionRepresentation (ZMod p) G X
  let e := permutationFunctionRepresentationSelfDual (k := ZMod p) (G := G) (X := X)
  let O := selfDualOrthogonalSubrepresentation rho e A
  have hO : O.toSubmodule ≠ ⊥ := by
    intro he
    have ha : A.toSubmodule.dualAnnihilator=⊥ := by
      apply le_antisymm ?_ bot_le
      intro ell hell
      have hv : e.symm ell ∈ O.toSubmodule := by
        change e (e.symm ell) ∈ A.toSubmodule.dualAnnihilator
        simpa only [e.apply_symm_apply] using hell
      rw [he] at hv
      have hz : e.symm ell=0 := hv
      have hz' := congrArg e hz
      exact (Submodule.mem_bot (R := ZMod p)).mpr (by simpa using hz')
    have hd := Subspace.dualAnnihilator_dualCoannihilator_eq (W := A.toSubmodule)
    rw [ha,Submodule.dualCoannihilator_bot] at hd
    exact hproper hd.symm
  have hone := pGroup_permutation_subrepresentation_contains_one hG x O hO
  intro v hv
  change (PermutationAugmentation.coordinateSum (ZMod p) X) v=0
  change e (fun _ : X => (1 : ZMod p)) ∈ A.toSubmodule.dualAnnihilator at hone
  have hz := (Submodule.mem_dualAnnihilator _).mp hone v hv
  rw [permutationFunctionRepresentationSelfDual_apply] at hz
  simpa only [one_mul,PermutationAugmentation.coordinateSum] using hz

def permutationAugmentationSubrepresentation :
    Subrepresentation (permutationFunctionRepresentation (ZMod p) G X) where
  toSubmodule := PermutationAugmentation.space (ZMod p) X
  apply_mem_toSubmodule g v hv := by
    change PermutationAugmentation.coordinateSum (ZMod p) X
      (permutationFunctionRepresentation (ZMod p) G X g v)=0
    rw [PermutationAugmentation.coordinateSum_permutation]
    exact hv

theorem pGroup_augmentation_interval_fixed_lift
    (hG : IsPGroup p G)
    (A : Subrepresentation (permutationFunctionRepresentation (ZMod p) G X))
    (hA : A.toSubmodule < PermutationAugmentation.space (ZMod p) X) :
    ∃ v : X → ZMod p,
      v ∈ PermutationAugmentation.space (ZMod p) X ∧ v ∉ A.toSubmodule ∧
      ∀ g : G,permutationFunctionRepresentation (ZMod p) G X g v-v ∈ A.toSubmodule := by
  let R : Subrepresentation (permutationFunctionRepresentation (ZMod p) G X) :=
    permutationAugmentationSubrepresentation
  let S := nestedSubrepresentation A R hA.le
  have hproper : S.toSubmodule ≠ ⊤ := by
    intro he
    obtain ⟨v,hv,hnot⟩ := SetLike.exists_of_lt hA
    have hm : (⟨v,hv⟩ : R.toSubmodule) ∈ S.toSubmodule := by
      rw [he]
      exact Submodule.mem_top
    exact hnot hm
  obtain ⟨v,hv,hfixed⟩ := pGroup_invariant_interval_fixed_lift hG R.toRepresentation S hproper
  refine ⟨v.val,v.property,?_,?_⟩
  · exact hv
  · intro g
    exact hfixed g

end SymmetricSubgroupAsymptotics
