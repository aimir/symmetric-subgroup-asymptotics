import SymmetricSubgroupAsymptotics.PermutationBinaryFourSection
import SymmetricSubgroupAsymptotics.SchurPGroupCapacity

/-! Pointwise multiplication is essential here. A nonzero invariant
annihilator in a transitive defining-characteristic permutation module
contains the constant function one. Thus T not contained in A makes its
actual pointwise annihilator modulo A zero. No convolution product is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {p : ℕ} [Fact p.Prime] {G X : Type} [Group G]
    [MulAction G X] [Finite X] [MulAction.IsPretransitive G X]

theorem pGroup_permutation_subrepresentation_contains_one
    (hG : IsPGroup p G) (x : X)
    (S : Subrepresentation (permutationFunctionRepresentation (ZMod p) G X))
    (hne : S.toSubmodule ≠ ⊥) : (fun _ : X => (1 : ZMod p)) ∈ S.toSubmodule := by
  letI : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨v,hv,hfixed⟩ := pGroup_representation_nonzero_fixed hG S.toRepresentation
  let f : (permutationFunctionRepresentation (ZMod p) G X).invariants :=
    ⟨v.val,fun g => congrArg Subtype.val (hfixed g)⟩
  have he : (fun _ : X => v.val x)=v.val := by
    exact congrArg Subtype.val
      ((PermutationBinaryFourSection.fixedEval (k := ZMod p) (G := G) x).symm_apply_apply f)
  have hc : v.val x ≠ 0 := by
    intro hz
    apply hv
    apply Subtype.ext
    rw [←he,hz]
    rfl
  have hm := S.toSubmodule.smul_mem (v.val x)⁻¹ v.property
  have hunit : (v.val x)⁻¹ • v.val=(fun _ : X => (1 : ZMod p)) := by
    rw [←he]
    funext y
    exact inv_mul_cancel₀ hc
  rw [hunit] at hm
  exact hm

def permutationPointwiseAnnihilator
    (A T : Subrepresentation (permutationFunctionRepresentation (ZMod p) G X)) :
    Subrepresentation (permutationFunctionRepresentation (ZMod p) G X) where
  toSubmodule := {
    carrier := {v | ∀ t ∈ T.toSubmodule,(fun x => v x*t x) ∈ A.toSubmodule}
    zero_mem' := by
      intro t ht
      have he : (fun x => (0 : X → ZMod p) x*t x)=(0 : X → ZMod p) := by
        funext x
        exact zero_mul _
      rw [he]
      exact A.toSubmodule.zero_mem
    add_mem' := by
      intro v w hv hw t ht
      have he : (fun x => (v+w) x*t x)=(fun x => v x*t x)+(fun x => w x*t x) := by
        funext x
        exact add_mul _ _ _
      rw [he]
      exact A.toSubmodule.add_mem (hv t ht) (hw t ht)
    smul_mem' := by
      intro c v hv t ht
      have he : (fun x => (c • v) x*t x)=c • (fun x => v x*t x) := by
        funext x
        exact mul_assoc _ _ _
      rw [he]
      exact A.toSubmodule.smul_mem c (hv t ht) }
  apply_mem_toSubmodule g v hv := by
    intro t ht
    have hm := A.apply_mem_toSubmodule g
      (hv (permutationFunctionRepresentation (ZMod p) G X g⁻¹ t)
        (T.apply_mem_toSubmodule g⁻¹ ht))
    convert hm using 1
    funext x
    simp only [permutationFunctionRepresentation_apply,inv_inv,smul_inv_smul]

theorem permutationPointwiseAnnihilator_eq_bot_of_not_le
    (hG : IsPGroup p G) (x : X)
    (A T : Subrepresentation (permutationFunctionRepresentation (ZMod p) G X))
    (hnot : ¬T.toSubmodule ≤ A.toSubmodule) :
    (permutationPointwiseAnnihilator A T).toSubmodule=⊥ := by
  by_contra hne
  have hone := pGroup_permutation_subrepresentation_contains_one hG x
    (permutationPointwiseAnnihilator A T) hne
  apply hnot
  intro t ht
  have hm := hone t ht
  simpa only [one_mul] using hm

end SymmetricSubgroupAsymptotics
