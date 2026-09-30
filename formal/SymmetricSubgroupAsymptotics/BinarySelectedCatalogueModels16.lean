import SymmetricSubgroupAsymptotics.BinaryCoordinateSplitAction
import SymmetricSubgroupAsymptotics.BinaryPairSplitRecognition
import SymmetricSubgroupAsymptotics.BinarySelectedAxisAugmentation
import SymmetricSubgroupAsymptotics.GeneratedPairBindings.PilotBinding16T1086
import SymmetricSubgroupAsymptotics.GeneratedPairBindings.PilotBinding16T1098

/-!
# The first two selected coordinate models in the degree-sixteen catalogue

Literal generator words identify the full degree-eight tops.  The reversible
kernel charts identify the correlated flip modules by their six checked basis
vectors and the two selected orbit-sum equations.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics

theorem relabelSubgroup_closure_range {I J κ : Type}
    (e : I ≃ J) (generators : κ → Equiv.Perm I) :
    relabelSubgroup e (Subgroup.closure (Set.range generators))=
      Subgroup.closure (Set.range (fun k => e.permCongr (generators k))) := by
  unfold relabelSubgroup
  change Subgroup.map e.permCongrHom.toMonoidHom
      (Subgroup.closure (Set.range generators)) = _
  rw [MonoidHom.map_closure]
  apply congrArg Subgroup.closure
  ext p
  constructor
  · rintro ⟨q,⟨k,rfl⟩,rfl⟩
    exact ⟨k,rfl⟩
  · rintro ⟨k,rfl⟩
    exact ⟨generators k,⟨k,rfl⟩,rfl⟩

namespace BinarySelectedCatalogue16T1086

def labelRelabel : Equiv.Perm (Fin 8) where
  toFun x := (#[0,2,4,6,1,3,5,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,4,1,5,2,6,3,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def sourceGenerators (j : Fin 2) : Equiv.Perm (Fin 8) :=
  labelRelabel.permCongr (BinaryTopSource056.generators j)

private def sourceToTarget : BinaryNormalGeneratorWords sourceGenerators
    BinaryMenuCayley8T10.generators where
  words j := if j.val<1 then [1,0,1,1,1] else [0,1,1,1]
  equations := by decide +kernel

private def targetToSource : BinaryNormalGeneratorWords
    BinaryMenuCayley8T10.generators sourceGenerators where
  words j := if j.val<1 then [1,0,1,1,1] else [0,1,1,1]
  equations := by decide +kernel

theorem top_eq :
    relabelSubgroup labelRelabel BinaryPairBinding16T1086.physicalFrame.top.range=
      BinarySelectedAxis8T10.Action := by
  rw [BinaryPairBinding16T1086.top_range,
    relabelSubgroup_closure_range labelRelabel BinaryTopSource056.generators]
  exact le_antisymm sourceToTarget.closure_le targetToSource.closure_le

theorem module_eq :
    binaryRelabelModule labelRelabel BinaryKernelAxes097.kernelChart.space=
      BinarySelectedAxis8T10.selectedAugmentation := by
  apply Submodule.eq_of_le_of_finrank_le
  · intro a ha
    obtain ⟨v,hv,rfl⟩ := ha
    have hsource : BinaryKernelAxes097.kernelChart.space≤
        BinarySelectedAxis8T10.selectedAugmentation.comap
          (binaryFunctionRelabel labelRelabel).toLinearMap := by
      apply BinaryKernelAxes097.kernelChart.le_of_basis_mem
      intro i
      change binaryFunctionRelabel labelRelabel
        (BinaryKernelAxes097.kernelChart.inclusion (Pi.single i 1))∈
          BinarySelectedAxis8T10.selectedAugmentation
      rw [BinarySelectedAxis8T10.mem_selectedAugmentation_iff]
      revert i
      decide +kernel
    exact hsource hv
  · have htarget : Module.finrank (ZMod 2)
        BinarySelectedAxis8T10.selectedAugmentation=6 := by
      exact PermutationBinaryTwoOrbitSplit.twoOrbitAugmentation_finrank
        BinarySelectedAxis8T10.selectedAxis
        BinarySelectedAxis8T10.selectedLeftOrbit
        BinarySelectedAxis8T10.selectedRightOrbit
        BinarySelectedAxis8T10.selected_orbits_ne (Nat.card_fin 8)
    change Module.finrank (ZMod 2) BinarySelectedAxis8T10.selectedAugmentation≤
      Module.finrank (ZMod 2)
        (BinaryKernelAxes097.kernelChart.space.map
          (binaryFunctionRelabel labelRelabel).toLinearMap)
    rw [(binaryFunctionRelabel labelRelabel).finrank_map_eq,
      BinaryKernelAxes097.kernelChart.finrank]
    change Module.finrank (ZMod 2) BinarySelectedAxis8T10.selectedAugmentation≤6
    rw [htarget]

/-- The literal 16T1086 generators have no retained affine twist. -/
theorem original_eq_physical_split :
    BinaryPairBinding16T1086.Original=
      BinaryPairBinding16T1086.physicalFrame.splitAffineAction := by
  apply BinaryPairBinding16T1086.physicalFrame.eq_splitAffineAction_of_generators
    BinaryPairBinding16T1086.generators BinaryPairBinding16T1086.generators_full
  intro j
  rw [BinaryPairBinding16T1086.kernel_space]
  rw [BinaryKernelAxes097.kernelChart.mem_iff]
  revert j
  unfold BinaryPairFrame.affineTranslation BinaryPairFrame.offset
  simp only [BinaryPairBinding16T1086.physicalFrame,
    BinaryPairBinding16T1086.generators,
    BinaryPairFrame.ofGenerators_top_generator]
  decide +kernel

theorem physical_split_eq_canonical :
    relabelSubgroup
        (BinaryPairBinding16T1086.physicalFrame.frame.symm.trans
          (binaryCoordinateRelabel labelRelabel))
        BinaryPairBinding16T1086.physicalFrame.splitAffineAction=
      binaryCoordinateSplitAction BinarySelectedAxis8T10.Action
        BinarySelectedAxis8T10.selectedAugmentation := by
  rw [← relabelSubgroup_trans,
    BinaryPairBinding16T1086.physicalFrame.relabelSubgroup_frame_symm_splitAffineAction,
    relabelSubgroup_binaryCoordinateSplitAction,
    BinaryPairBinding16T1086.kernel_space,top_eq,module_eq]

theorem physical_original_eq_canonical :
    relabelSubgroup
        (BinaryPairBinding16T1086.physicalFrame.frame.symm.trans
          (binaryCoordinateRelabel labelRelabel))
        BinaryPairBinding16T1086.Original=
      binaryCoordinateSplitAction BinarySelectedAxis8T10.Action
        BinarySelectedAxis8T10.selectedAugmentation := by
  calc
    relabelSubgroup
        (BinaryPairBinding16T1086.physicalFrame.frame.symm.trans
          (binaryCoordinateRelabel labelRelabel))
        BinaryPairBinding16T1086.Original =
      relabelSubgroup
        (BinaryPairBinding16T1086.physicalFrame.frame.symm.trans
          (binaryCoordinateRelabel labelRelabel))
        BinaryPairBinding16T1086.physicalFrame.splitAffineAction :=
      congrArg (relabelSubgroup
        (BinaryPairBinding16T1086.physicalFrame.frame.symm.trans
          (binaryCoordinateRelabel labelRelabel))) original_eq_physical_split
    _ = _ := physical_split_eq_canonical

end BinarySelectedCatalogue16T1086

namespace BinarySelectedCatalogue16T1098

def labelRelabel : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,7,3,4,5,6] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,4,5,6,7,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def sourceGenerators (j : Fin 3) : Equiv.Perm (Fin 8) :=
  labelRelabel.permCongr (BinaryTopSource046.generators j)

private def sourceToTarget : BinaryNormalGeneratorWords sourceGenerators
    BinaryMenuCayley8T9.generators where
  words j := if j.val<1 then [3] else if j.val<2 then [0,1,3] else [1,3,2]
  equations := by decide +kernel

private def targetToSource : BinaryNormalGeneratorWords
    BinaryMenuCayley8T9.generators sourceGenerators where
  words j := if j.val<2 then (if j.val<1 then [2,2] else [0,1,2,2])
    else if j.val<3 then [2,1] else [0]
  equations := by decide +kernel

theorem top_eq :
    relabelSubgroup labelRelabel BinaryPairBinding16T1098.physicalFrame.top.range=
      BinarySelectedAxis8T9.Action := by
  rw [BinaryPairBinding16T1098.top_range,
    relabelSubgroup_closure_range labelRelabel BinaryTopSource046.generators]
  exact le_antisymm sourceToTarget.closure_le targetToSource.closure_le

theorem module_eq :
    binaryRelabelModule labelRelabel BinaryKernelAxes077.kernelChart.space=
      BinarySelectedAxis8T9.selectedAugmentation := by
  apply Submodule.eq_of_le_of_finrank_le
  · intro a ha
    obtain ⟨v,hv,rfl⟩ := ha
    have hsource : BinaryKernelAxes077.kernelChart.space≤
        BinarySelectedAxis8T9.selectedAugmentation.comap
          (binaryFunctionRelabel labelRelabel).toLinearMap := by
      apply BinaryKernelAxes077.kernelChart.le_of_basis_mem
      intro i
      change binaryFunctionRelabel labelRelabel
        (BinaryKernelAxes077.kernelChart.inclusion (Pi.single i 1))∈
          BinarySelectedAxis8T9.selectedAugmentation
      rw [BinarySelectedAxis8T9.mem_selectedAugmentation_iff]
      revert i
      decide +kernel
    exact hsource hv
  · have htarget : Module.finrank (ZMod 2)
        BinarySelectedAxis8T9.selectedAugmentation=6 := by
      exact PermutationBinaryTwoOrbitSplit.twoOrbitAugmentation_finrank
        BinarySelectedAxis8T9.selectedAxis
        BinarySelectedAxis8T9.selectedLeftOrbit
        BinarySelectedAxis8T9.selectedRightOrbit
        BinarySelectedAxis8T9.selected_orbits_ne (Nat.card_fin 8)
    change Module.finrank (ZMod 2) BinarySelectedAxis8T9.selectedAugmentation≤
      Module.finrank (ZMod 2)
        (BinaryKernelAxes077.kernelChart.space.map
          (binaryFunctionRelabel labelRelabel).toLinearMap)
    rw [(binaryFunctionRelabel labelRelabel).finrank_map_eq,
      BinaryKernelAxes077.kernelChart.finrank]
    change Module.finrank (ZMod 2) BinarySelectedAxis8T9.selectedAugmentation≤6
    rw [htarget]

/-- The literal 16T1098 generators have no retained affine twist. -/
theorem original_eq_physical_split :
    BinaryPairBinding16T1098.Original=
      BinaryPairBinding16T1098.physicalFrame.splitAffineAction := by
  apply BinaryPairBinding16T1098.physicalFrame.eq_splitAffineAction_of_generators
    BinaryPairBinding16T1098.generators BinaryPairBinding16T1098.generators_full
  intro j
  rw [BinaryPairBinding16T1098.kernel_space]
  rw [BinaryKernelAxes077.kernelChart.mem_iff]
  revert j
  unfold BinaryPairFrame.affineTranslation BinaryPairFrame.offset
  simp only [BinaryPairBinding16T1098.physicalFrame,
    BinaryPairBinding16T1098.generators,
    BinaryPairFrame.ofGenerators_top_generator]
  decide +kernel

theorem physical_split_eq_canonical :
    relabelSubgroup
        (BinaryPairBinding16T1098.physicalFrame.frame.symm.trans
          (binaryCoordinateRelabel labelRelabel))
        BinaryPairBinding16T1098.physicalFrame.splitAffineAction=
      binaryCoordinateSplitAction BinarySelectedAxis8T9.Action
        BinarySelectedAxis8T9.selectedAugmentation := by
  rw [← relabelSubgroup_trans,
    BinaryPairBinding16T1098.physicalFrame.relabelSubgroup_frame_symm_splitAffineAction,
    relabelSubgroup_binaryCoordinateSplitAction,
    BinaryPairBinding16T1098.kernel_space,top_eq,module_eq]

theorem physical_original_eq_canonical :
    relabelSubgroup
        (BinaryPairBinding16T1098.physicalFrame.frame.symm.trans
          (binaryCoordinateRelabel labelRelabel))
        BinaryPairBinding16T1098.Original=
      binaryCoordinateSplitAction BinarySelectedAxis8T9.Action
        BinarySelectedAxis8T9.selectedAugmentation := by
  calc
    relabelSubgroup
        (BinaryPairBinding16T1098.physicalFrame.frame.symm.trans
          (binaryCoordinateRelabel labelRelabel))
        BinaryPairBinding16T1098.Original =
      relabelSubgroup
        (BinaryPairBinding16T1098.physicalFrame.frame.symm.trans
          (binaryCoordinateRelabel labelRelabel))
        BinaryPairBinding16T1098.physicalFrame.splitAffineAction :=
      congrArg (relabelSubgroup
        (BinaryPairBinding16T1098.physicalFrame.frame.symm.trans
          (binaryCoordinateRelabel labelRelabel))) original_eq_physical_split
    _ = _ := physical_split_eq_canonical

end BinarySelectedCatalogue16T1098

end SymmetricSubgroupAsymptotics
