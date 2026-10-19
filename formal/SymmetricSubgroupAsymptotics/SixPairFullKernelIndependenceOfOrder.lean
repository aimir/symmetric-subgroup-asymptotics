import SymmetricSubgroupAsymptotics.SixPairThreePairOriginalOrder

/-! Recognition of full physical independence from the actual kernel
order. The kernel already injects into the 8^3 permitted original local
permutations; actual order512 makes that same map onto. No table metadata
or abstract owner predicate is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairFullKernelIndependenceOfOrder
open BinaryTwoLayerLocalClassTwo

variable {X I : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I)
  (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))

private theorem local_card : Nat.card SixPairThreePairOriginalOrder.Local=8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- The order assertion is about the literal original coordinate kernel. -/
theorem independent
    (hcard : Nat.card (SixPairNestedTopFrames.nestedFrame F E).top.ker=512) :
    SixPairIndependentKernelNormalCommutators.Independent F E := by
  let C := SixPairNestedTopFrames.nestedFrame F E
  let f : C.top.ker → (Fin 3 → SixPairThreePairOriginalOrder.Local) := fun k j =>
    ⟨C.kernelCoordinate j k,SixPairThreePairKernelClassTwo.coordinate_preserves F E j k⟩
  have hi : Function.Injective f := by
    intro a b h
    apply C.kernelCoordinates_joint_injective
    funext j
    exact congrArg (fun v : Fin 3 → SixPairThreePairOriginalOrder.Local => (v j).val) h
  have hc : Nat.card C.top.ker=Nat.card (Fin 3 → SixPairThreePairOriginalOrder.Local) := by
    rw [hcard,Nat.card_fun,local_card,Nat.card_fin]
    norm_num
  have hs : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).mpr ⟨hi,hc⟩).surjective
  intro v hv
  obtain ⟨k,hk⟩ := hs (fun j => ⟨v j,hv j⟩)
  refine ⟨k,?_⟩
  intro j
  exact congrArg (fun w : Fin 3 → SixPairThreePairOriginalOrder.Local => (w j).val) hk

end SymmetricSubgroupAsymptotics.SixPairFullKernelIndependenceOfOrder
