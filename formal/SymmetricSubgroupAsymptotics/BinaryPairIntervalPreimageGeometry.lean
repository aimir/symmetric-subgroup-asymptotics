import SymmetricSubgroupAsymptotics.BinaryPairIntervalKernelStabilizer
import SymmetricSubgroupAsymptotics.BinaryPairLayerPreimageCards

/-! Exact interval-preimage geometry for the SAME pair action. The
selected constant flip has 2^w times the original lower-denominator
cardinality fixed modulo that denominator. The full interval preimage
has no nontrivial top stabilizer, including arbitrary actual offsets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance intervalPreimageGeometryPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

theorem pairSum_preimage_stable
    (A : Subrepresentation (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin w)))
    (u : U) (v : X → ZMod 2) (hv : v∈A.toSubmodule.comap F.pairSum) :
    permutationFunctionRepresentation (ZMod 2) U X u v ∈ A.toSubmodule.comap F.pairSum := by
  change F.pairSum (permutationFunctionRepresentation (ZMod 2) U X u v)∈A.toSubmodule
  have he := Representation.IntertwiningMap.isIntertwining _ _ F.pairSumIntertwiner u v
  change F.pairSum (permutationFunctionRepresentation (ZMod 2) U X u v)=
    permutationFunctionRepresentation (ZMod 2) F.top.range (Fin w)
      (F.top.rangeRestrict u) (F.pairSum v) at he
  rw [he]
  exact A.apply_mem_toSubmodule (F.top.rangeRestrict u) hv

theorem pairSum_preimage_interval_displacement
    (A T : Subrepresentation (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin w)))
    (hdisp : ∀ (t : F.top.range) (a : Fin w → ZMod 2),a∈T.toSubmodule →
      permutationFunctionRepresentation (ZMod 2) F.top.range (Fin w) t a-a∈A.toSubmodule)
    (u : U) (v : X → ZMod 2) (hv : v∈T.toSubmodule.comap F.pairSum) :
    permutationFunctionRepresentation (ZMod 2) U X u v-v ∈ A.toSubmodule.comap F.pairSum := by
  change F.pairSum (permutationFunctionRepresentation (ZMod 2) U X u v-v)∈A.toSubmodule
  have he := Representation.IntertwiningMap.isIntertwining _ _ F.pairSumIntertwiner u v
  change F.pairSum (permutationFunctionRepresentation (ZMod 2) U X u v)=
    permutationFunctionRepresentation (ZMod 2) F.top.range (Fin w)
      (F.top.rangeRestrict u) (F.pairSum v) at he
  rw [map_sub,he]
  exact hdisp (F.top.rangeRestrict u) (F.pairSum v) hv

omit [Finite X] in
theorem constant_flip_displacement (z : F.top.ker) (hz : F.bits z=(fun _ => 1))
    (v : X → ZMod 2) :
    permutationFunctionRepresentation (ZMod 2) U X z.val v-v=F.pairConstant (F.pairSum v) := by
  rw [F.kernel_displacement_eq_pairConstant_product,hz]
  congr 1
  funext i
  exact one_mul _

theorem constant_flip_fixed_augmentation_card
    (A : Submodule (ZMod 2) (Fin w → ZMod 2))
    (hA : A≤PermutationAugmentation.space (ZMod 2) (Fin w))
    (z : F.top.ker) (hz : F.bits z=(fun _ => 1)) :
    Nat.card {v : X → ZMod 2 //
      v∈PermutationAugmentation.space (ZMod 2) X ∧
      permutationFunctionRepresentation (ZMod 2) U X z.val v-v∈A.map F.pairConstant}=
      2^w*Nat.card A := by
  have hiff (v : X → ZMod 2) :
      (v∈PermutationAugmentation.space (ZMod 2) X ∧
        permutationFunctionRepresentation (ZMod 2) U X z.val v-v∈A.map F.pairConstant) ↔
      v∈A.comap F.pairSum := by
    rw [F.constant_flip_displacement z hz]
    constructor
    · rintro ⟨_,a,ha,he⟩
      change F.pairSum v∈A
      rw [←F.pairConstant_injective he]
      exact ha
    · intro hv
      exact ⟨F.pairSum_preimage_le_augmentation A hA hv,⟨F.pairSum v,hv,rfl⟩⟩
  let e : {v : X → ZMod 2 //
      v∈PermutationAugmentation.space (ZMod 2) X ∧
      permutationFunctionRepresentation (ZMod 2) U X z.val v-v∈A.map F.pairConstant} ≃
      A.comap F.pairSum := {
    toFun v := ⟨v.val,(hiff v.val).mp v.property⟩
    invFun v := ⟨v.val,(hiff v.val).mpr v.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  exact (Nat.card_congr e).trans (F.pairSum_preimage_card A)

theorem interval_preimage_stabilizer_card_le_one
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U) (i : Fin w)
    (A T : Subrepresentation (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin w)))
    (hsmall : 2*Module.finrank (ZMod 2) A.toSubmodule < w)
    (hnot : ¬T.toSubmodule ≤ A.toSubmodule) :
    Nat.card {u : U // ∀ v : X → ZMod 2,v∈T.toSubmodule.comap F.pairSum →
      permutationFunctionRepresentation (ZMod 2) U X u v-v∈A.toSubmodule.map F.pairConstant}≤1 := by
  let f : {u : U // ∀ v : X → ZMod 2,v∈T.toSubmodule.comap F.pairSum →
      permutationFunctionRepresentation (ZMod 2) U X u v-v∈A.toSubmodule.map F.pairConstant} → Unit :=
    fun _ => ()
  have hf : Function.Injective f := by
    intro a b _
    apply Subtype.ext
    exact (F.eq_one_of_interval_preimage_displacement hU i A T hsmall hnot a.val a.property).trans
      (F.eq_one_of_interval_preimage_displacement hU i A T hsmall hnot b.val b.property).symm
  simpa only [Nat.card_unique] using Nat.card_le_card_of_injective f hf

end SymmetricSubgroupAsymptotics.BinaryPairFrame
