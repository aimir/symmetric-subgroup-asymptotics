import SymmetricSubgroupAsymptotics.BinarySplitElementary16PhiZeroStabilizer
import SymmetricSubgroupAsymptotics.BinaryPairOriginalZeroRowEnumeration
import SymmetricSubgroupAsymptotics.BinaryEightOriginalRowActions
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryHeads

/-! The selected sixteen affine rows enumerate the SAME original zero model.
Only eight top permutations and two kernel vectors are tested; row
completeness follows from the exact original semidirect cardinality. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinarySplitElementary16PhiZeroOriginalRows

open BinarySplitElementary16PhiZeroStabilizer

private def topBase (i : Fin 8) : Equiv.Perm (Fin 8) :=
  topPermutation ⟨2 * i.val, by have hi := i.isLt; omega⟩
private def offsetBase (i : Fin 2) : Fin 8 → ZMod 2 :=
  destinationOffset ⟨i.val, by have hi := i.isLt; omega⟩

private theorem topBase_original : ∀ i : Fin 8, ∃ j : Fin 8,
    topBase i = (BinaryEightOriginalRowActions.regularRow j).val := by decide +kernel
private theorem offsetBase_mem : ∀ i : Fin 2,
    offsetBase i ∈ (BinaryRegularEightNaturalRegistry.charts 23).2.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel
private theorem topBase_injective : Function.Injective topBase := by
  change ∀ i j : Fin 8, topBase i = topBase j → i = j
  decide +kernel
private theorem offsetBase_injective : Function.Injective offsetBase := by
  change ∀ i j : Fin 2, offsetBase i = offsetBase j → i = j
  decide +kernel
private theorem top_decomposition : ∀ i : Fin 16,
    topPermutation i = topBase ⟨i.val / 2, by have hi := i.isLt; omega⟩ := by decide +kernel
private theorem offset_decomposition : ∀ i : Fin 16,
    destinationOffset i = offsetBase ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

theorem coordinates_injective (i j : Fin 16)
    (ht : topPermutation i = topPermutation j)
    (ha : destinationOffset i = destinationOffset j) : i = j := by
  have hq := congrArg Fin.val (topBase_injective
    ((top_decomposition i).symm.trans (ht.trans (top_decomposition j))))
  have hr := congrArg Fin.val (offsetBase_injective
    ((offset_decomposition i).symm.trans (ha.trans (offset_decomposition j))))
  apply Fin.ext
  change i.val / 2 = j.val / 2 at hq
  change i.val % 2 = j.val % 2 at hr
  omega

theorem top_mem (i : Fin 16) :
    topPermutation i ∈ BinaryEightOriginalRowActions.regularH := by
  rw [top_decomposition]
  obtain ⟨j, hj⟩ := topBase_original ⟨i.val / 2, by have hi := i.isLt; omega⟩
  rw [hj]
  exact (BinaryEightOriginalRowActions.regularRow j).property

theorem offset_mem (i : Fin 16) :
    destinationOffset i ∈ (BinaryRegularEightNaturalRegistry.charts 23).2.space := by
  rw [offset_decomposition]
  exact offsetBase_mem _

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8))

theorem kernel_le_original_zero_frame (hzero : U = F.splitAffineAction)
    (hH : F.top.range = BinaryEightOriginalRowActions.regularH)
    (hK : F.kernelSpace = (BinaryRegularEightNaturalRegistry.charts 23).2.space)
    (D : Subgroup U) (hD : 2 < Nat.card D)
    (K : Submodule (ZMod 2) (Fin 16 → ZMod 2))
    (hfixed : ∀ d : D, ∀ v ∈ K,
      F.originalCoordinateRepresentation (d : U) v - v ∈ radical.space) :
    K ≤ state.space := by
  have ht (i : Fin 16) : topPermutation i ∈ F.top.range := by
    rw [hH]
    exact top_mem i
  have ha (i : Fin 16) : destinationOffset i ∈ F.kernelSpace := by
    rw [hK]
    exact offset_mem i
  let row := F.originalAffineRows hzero topPermutation destinationOffset ht ha
  have hcard : Nat.card F.kernelSpace * Nat.card F.top.range = 16 := by
    rw [hK, hH]
    have hker : Nat.card (BinaryRegularEightNaturalRegistry.charts 23).2.space = 2 :=
      (BinaryRegularEightNaturalRegistry.charts 23).2.card
    rw [hker, BinaryMenuCayley8T3.exact_card]
  have hrow : Function.Bijective row :=
    F.originalAffineRows_bijective hzero topPermutation destinationOffset ht ha coordinates_injective hcard
  apply BinarySplitElementary16PhiZeroStabilizer.kernel_le row hrow
    F.originalCoordinateRepresentation _ D hD K hfixed
  intro i
  exact F.originalCoordinateRepresentation_affineRow hzero topPermutation destinationOffset ht ha i

end SymmetricSubgroupAsymptotics.BinarySplitElementary16PhiZeroOriginalRows
