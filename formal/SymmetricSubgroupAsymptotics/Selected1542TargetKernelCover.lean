import SymmetricSubgroupAsymptotics.Selected1542SecondCenterData
import SymmetricSubgroupAsymptotics.Selected1542OriginalTargetMaps
import SymmetricSubgroupAsymptotics.FiniteKernelCosetGrid

/-! The sixteen literal target-kernel states cover the actual original
binary kernel after adjoining the exact original L64 chart. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure

local instance targetKernelCover_preimageFintype : Fintype originalPreimage := Fintype.ofFinite _
local instance targetKernelCover_rangeNormal : originalPreimage.subtype.range.Normal := by
  rw [Subgroup.range_subtype]
  infer_instance

def secondCenterTargetCubic (i : Fin 48) : CyclicThree :=
  ((word i).map (fun j => NaturalA4ScalarFourHead.top (alternatingGenerator j 0))).prod

set_option maxHeartbeats 1000000 in
private theorem targetKernelCover_receipt : ∀ i : Fin 48,
    secondCenterTargetCubic i=1 → ∃ j : Fin 16, ∀ p : Fin 8,
      targetState i p=targetState (secondCenterTargetIndex j) p := by decide +kernel

private theorem targetStateElement_word (i : Fin 48) :
    targetStateElement i=((word i).map targetSource).prod := by
  apply Subtype.ext
  change targetState i=literalTarget.subtype (((word i).map targetSource).prod)
  rw [map_list_prod,List.map_map]
  rfl

private theorem targetCubic_state (i : Fin 48) :
    ActualRepeatedAlternatingCentralCoordinates.top targetAlternating 0
      (targetStateElement i)=secondCenterTargetCubic i := by
  rw [targetStateElement_word,map_list_prod,List.map_map]
  change ((word i).map (fun j => NaturalA4ScalarFourHead.top
    (targetAlternating (targetSource j) 0))).prod=
      ((word i).map (fun j => NaturalA4ScalarFourHead.top (alternatingGenerator j 0))).prod
  simp only [targetAlternating_generator]

theorem actual_target_kernel_cover (h : literalTarget)
    (hh : ActualRepeatedAlternatingCentralCoordinates.top targetAlternating 0 h=1) :
    ∃ j : Fin 16, targetStateElement (secondCenterTargetIndex j)=h := by
  obtain ⟨i,rfl⟩ := actualQuotientGraph.certificate.sourceElement_surjective h
  have hi : secondCenterTargetCubic i=1 := (targetCubic_state i).symm.trans hh
  obtain ⟨j,hj⟩ := targetKernelCover_receipt i hi
  refine ⟨j,?_⟩
  apply Subtype.ext
  apply Equiv.ext
  intro p
  exact (hj p).symm

theorem original_binary_kernel_grid (g : Original) (hg : g∈originalBinaryKernel) :
    ∃ (r : Fin 16) (i : Fin 64),
      g=originalState (secondCenterTargetIndex r)*preimageOriginal i := by
  let B := (ActualRepeatedAlternatingCentralCoordinates.top targetAlternating 0).ker
  have hcover : ∀ h∈B, ∃ r : Fin 16,
      originalToTarget (originalState (secondCenterTargetIndex r))=h := by
    intro h hh
    obtain ⟨r,hr⟩ := actual_target_kernel_cover h hh
    exact ⟨r,(originalToTarget_state _).trans hr⟩
  have hh : originalToTarget g∈B := hg
  exact exists_kernel_coset_grid preimageTable originalToTarget originalToTarget_ker B
    (fun r => originalState (secondCenterTargetIndex r)) hcover g hh

end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
