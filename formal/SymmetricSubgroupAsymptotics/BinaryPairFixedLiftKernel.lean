import SymmetricSubgroupAsymptotics.BinaryPairMaximalSection
import SymmetricSubgroupAsymptotics.PermutationBinaryFourSection
import Mathlib.GroupTheory.Index

/-! A fixed quotient lift with nonzero displacement forces the whole
original pair kernel to consist of constant flips. This is an injection
of the actual kernel, not a comparison of abstract quotient dimensions. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)
    [MulAction.IsPretransitive U X]
    (m : X → ZMod 2) (hsum : F.pairSum m=(fun _ => 1))

include hsum in
private theorem fixedLift_displacement_bits (z : F.top.ker) (i : I) :
    (permutationFunctionRepresentation (ZMod 2) U X (z:U) m-m) (F.frame (i,0))=
      F.bits z i := by
  have hinv : F.bits z⁻¹ i=F.bits z i := by
    have hi := congrArg (fun a : Multiplicative (I → ZMod 2) => a.toAdd i)
      (F.bitsHom.map_inv z)
    change F.bits z⁻¹ i = -F.bits z i at hi
    simpa only [CharTwo.neg_eq] using hi
  change m ((((z⁻¹ : F.top.ker):U):Equiv.Perm X) (F.frame (i,0)))-m (F.frame (i,0))=_
  rw [F.kernel_action_frame,zero_add,hinv]
  have hbits : ∀ b : ZMod 2, b=0 ∨ b=1 := by decide +kernel
  rcases hbits (F.bits z i) with hzero | hone
  · rw [hzero,sub_self]
  · rw [hone,CharTwo.sub_eq_add,add_comm]
    exact congrFun hsum i

variable (hfixed : ∀ u : U,
  permutationFunctionRepresentation (ZMod 2) U X u m-m∈
    (permutationFunctionRepresentation (ZMod 2) U X).invariants)

include hsum hfixed in
theorem kernel_bits_constant_of_fixed_lift (i : I) (z : F.top.ker) (j : I) :
    F.bits z j=F.bits z i := by
  let d : (permutationFunctionRepresentation (ZMod 2) U X).invariants :=
    ⟨permutationFunctionRepresentation (ZMod 2) U X (z:U) m-m,hfixed (z:U)⟩
  have he := (PermutationBinaryFourSection.fixedEval (k := ZMod 2) (G := U)
    (F.frame (i,0))).symm_apply_apply d
  have hv := congrArg
    (fun v : (permutationFunctionRepresentation (ZMod 2) U X).invariants =>
      (v : X → ZMod 2) (F.frame (j,0))) he
  have hconst : d.1 (F.frame (j,0))=d.1 (F.frame (i,0)) := hv.symm
  exact (F.fixedLift_displacement_bits m hsum z j).symm.trans
    (hconst.trans (F.fixedLift_displacement_bits m hsum z i))

include hsum hfixed in
/-- Evaluate the actual original kernel at one original pair. -/
theorem kernel_eval_injective_of_fixed_lift (i : I) :
    Function.Injective (fun z : F.top.ker => F.bits z i) := by
  intro z z' hz
  apply F.bitsHom_injective
  apply congrArg Multiplicative.ofAdd
  funext j
  exact (F.kernel_bits_constant_of_fixed_lift m hsum hfixed i z j).trans
    (hz.trans (F.kernel_bits_constant_of_fixed_lift m hsum hfixed i z' j).symm)

include hsum hfixed in
theorem kernel_card_le_two_of_fixed_lift (i : I) : Nat.card F.top.ker≤2 := by
  have h := Nat.card_le_card_of_injective _
    (F.kernel_eval_injective_of_fixed_lift m hsum hfixed i)
  simpa only [Nat.card_zmod] using h

include hsum hfixed in
/-- The complete original source cardinal is bounded using its actual
top range and its now proved original kernel bound. -/
theorem card_le_eight_of_fixed_lift [Finite X] (i : I)
    (htop : Nat.card F.top.range=4) : Nat.card U≤8 := by
  have hk := F.kernel_card_le_two_of_fixed_lift m hsum hfixed i
  have hc := F.top.ker.card_mul_index
  rw [Subgroup.index_ker,htop] at hc
  omega

end SymmetricSubgroupAsymptotics.BinaryPairFrame
