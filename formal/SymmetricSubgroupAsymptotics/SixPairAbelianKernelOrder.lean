import SymmetricSubgroupAsymptotics.BinaryTwoLayerLocalAbelianOrder
import SymmetricSubgroupAsymptotics.SixPairThreePairKernelClassTwo
import SymmetricSubgroupAsymptotics.FiniteTopSmallBinaryKernelRawSum

/-! Actual abelian local ranges have at most four elements each, so the
SAME coarse kernel has order at most64 and original group at most384.
Physical independence of the three local factors is not assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.SixPairAbelianKernelOrder
variable {X I : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I)
  (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))

 theorem kernel_card_le
    (hcomm : ∀ a b : (SixPairNestedTopFrames.nestedFrame F E).top.ker,a*b=b*a) :
    Nat.card (SixPairNestedTopFrames.nestedFrame F E).top.ker≤64 := by
  let C := SixPairNestedTopFrames.nestedFrame F E
  let L := fun i : Fin 3 => (C.kernelCoordinate i).range
  have hl (i : Fin 3) : Nat.card (L i)≤4 := by
    apply BinaryTwoLayerLocalAbelianOrder.card_le_four
    · intro a
      obtain ⟨u,hu⟩ := a.property
      rw [←hu]
      exact SixPairThreePairKernelClassTwo.coordinate_preserves F E i u
    · intro a b
      apply Subtype.ext
      obtain ⟨u,hu⟩ := a.property
      obtain ⟨v,hv⟩ := b.property
      change a.val*b.val=b.val*a.val
      rw [←hu,←hv,←map_mul,←map_mul,hcomm]
  let enc : C.top.ker → ((i : Fin 3) → L i) :=
    fun k i => (C.kernelCoordinate i).rangeRestrict k
  have hi : Function.Injective enc := by
    intro a b h
    apply C.kernelCoordinates_joint_injective
    funext i
    exact congrArg Subtype.val (congrFun h i)
  calc
    _ ≤ Nat.card ((i : Fin 3) → L i) := Nat.card_le_card_of_injective enc hi
    _ = ∏ i : Fin 3,Nat.card (L i) := Nat.card_pi
    _ ≤ ∏ _i : Fin 3,4 := Finset.prod_le_prod' (fun i _ => hl i)
    _ = 64 := by norm_num

 theorem original_card_le
    (hcomm : ∀ a b : (SixPairNestedTopFrames.nestedFrame F E).top.ker,a*b=b*a) :
    Nat.card U≤2^9 := by
  let C := SixPairNestedTopFrames.nestedFrame F E
  have hk := kernel_card_le F E hcomm
  have ht : Nat.card C.top.range≤6 :=
    FiniteTopKernelHomLiftCount.top_card_le_six C.top.range.subtype Subtype.val_injective
  have he := C.top.ker.card_mul_index
  rw [Subgroup.index_ker] at he
  exact he.symm.le.trans ((Nat.mul_le_mul hk ht).trans (by norm_num))

end SymmetricSubgroupAsymptotics.SixPairAbelianKernelOrder
