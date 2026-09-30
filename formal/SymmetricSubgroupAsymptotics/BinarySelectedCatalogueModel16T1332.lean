import SymmetricSubgroupAsymptotics.BinarySelectedCatalogueModels16
import SymmetricSubgroupAsymptotics.BinaryPairKernelCard
import SymmetricSubgroupAsymptotics.BinaryCarrierExactOrders16

/-!
# The selected 16T1332 split model

A small certificate on the literal five generators supplies the adjacent-pair
frame, the 8T18 top, and six reversible kernel basis words.  The already
proved exact original order then identifies the whole correlated kernel.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinarySelectedCatalogue16T1332

abbrev Original :=
  Subgroup.closure (Set.range BinaryActionData16.node1332Generators)

def generators (j : Fin 5) : Original :=
  ⟨BinaryActionData16.node1332Generators j,Subgroup.subset_closure ⟨j,rfl⟩⟩

theorem generators_full : Subgroup.closure (Set.range generators)=⊤ :=
  binaryNormal_full_generators_of_equiv BinaryActionData16.node1332Generators
    generators (MulEquiv.refl _) (fun _ => rfl)

def originalWord (ws : List (Fin 5)) : Original :=
  ⟨(ws.map BinaryActionData16.node1332Generators).prod,
    Subgroup.list_prod_mem _ (by
      intro x hx
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
      exact Subgroup.subset_closure ⟨j,rfl⟩)⟩

def frame : Fin 8 × ZMod 2 ≃ Fin 16 where
  toFun p := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] :
    Array (Fin 16))[2*p.1.val+p.2.val]!
  invFun x :=
    ((#[0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7] : Array (Fin 8))[x.val]!,
      (#[0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1] : Array (ZMod 2))[x.val]!)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def top0 : Equiv.Perm (Fin 8) := 1
private def top1 : Equiv.Perm (Fin 8) := 1

private def top2 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,2,1,0,7,6,5,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def top3 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,2,1,0,4,5,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[3,2,1,0,4,5,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def top4 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,5,4,7,1,2,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,4,5,6,2,1,0,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def tops (j : Fin 5) : Equiv.Perm (Fin 8) :=
  if j.val<2 then (if j.val<1 then top0 else top1)
  else if j.val<3 then top2 else if j.val<4 then top3 else top4

private theorem preserves : ∀ j,
    BinaryPairFrame.Preserves frame (BinaryActionData16.node1332Generators j)
      (tops j) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def physicalFrame : BinaryPairFrame Original (Fin 8) :=
  BinaryPairFrame.ofGenerators frame BinaryActionData16.node1332Generators
    tops preserves

theorem top_range :
    physicalFrame.top.range=Subgroup.closure (Set.range tops) := by
  exact BinaryPairFrame.ofGenerators_top_range frame
    BinaryActionData16.node1332Generators tops preserves

/-- The same label permutation which displays the selected 8T18 axis. -/
abbrev labelRelabel : Equiv.Perm (Fin 8) :=
  BinarySelectedCatalogue16T1098.labelRelabel

def sourceGenerators (j : Fin 5) : Equiv.Perm (Fin 8) :=
  labelRelabel.permCongr (tops j)

private def sourceToTarget : BinaryNormalGeneratorWords sourceGenerators
    BinaryMenuCayley8T18.generators where
  words j := if j.val<2 then [] else if j.val<3 then [0,4]
    else if j.val<4 then [0,3] else [1,3,2]
  equations := by decide +kernel

private def targetToSource : BinaryNormalGeneratorWords
    BinaryMenuCayley8T18.generators sourceGenerators where
  words j := if j.val<1 then [4,4]
    else if j.val<2 then [2,3,4,2,3,4]
    else if j.val<3 then [2,4,2,3]
    else if j.val<4 then [3,4,4] else [2,4,4]
  equations := by decide +kernel

theorem top_eq :
    relabelSubgroup labelRelabel physicalFrame.top.range=
      BinarySelectedAxis8T18.Action := by
  rw [top_range,relabelSubgroup_closure_range labelRelabel tops]
  exact le_antisymm sourceToTarget.closure_le targetToSource.closure_le

theorem top_card : Nat.card physicalFrame.top.range=32 := by
  calc
    Nat.card physicalFrame.top.range =
        Nat.card (relabelSubgroup labelRelabel physicalFrame.top.range) :=
      Nat.card_congr
        (BinaryPairFrame.sourceRelabelEquiv
          (U := physicalFrame.top.range) labelRelabel).toEquiv
    _ = Nat.card BinarySelectedAxis8T18.Action := by rw [top_eq]
    _ = 32 := BinaryMenuCayley8T18.exact_card

private def basisWords (i : Fin 6) : List (Fin 5) :=
  if i.val<3 then
    if i.val<1 then [1]
    else if i.val<2 then [0,1,3,4,1,3,4]
    else [0,1,3,1,4,1,3,4]
  else if i.val<4 then [1,3,4,0,3,4]
  else if i.val<5 then [0]
  else [1,4,1,4,1,4,4]

private theorem basis_action : ∀ i : Fin 6,∀ p : Fin 8 × ZMod 2,
    frame.symm ((originalWord (basisWords i) : Equiv.Perm (Fin 16)) (frame p))=
      (p.1,p.2+BinaryKernelAxes077.kernelChart.inclusion (Pi.single i 1) p.1) := by
  decide +kernel

theorem kernel_space :
    physicalFrame.kernelSpace=BinaryKernelAxes077.kernelChart.space := by
  apply physicalFrame.kernelSpace_eq_of_basis_and_card
    BinaryKernelAxes077.kernelChart
  · intro i
    exact physicalFrame.vector_mem_kernelSpace_of_action
      (originalWord (basisWords i))
      (BinaryKernelAxes077.kernelChart.inclusion (Pi.single i 1))
      (basis_action i)
  · rw [BinaryCarrierExactOrder16T1332.original_card,top_card]
    norm_num

theorem module_eq :
    binaryRelabelModule labelRelabel physicalFrame.kernelSpace=
      BinarySelectedAxis8T18.selectedAugmentation := by
  rw [kernel_space]
  calc
    binaryRelabelModule labelRelabel BinaryKernelAxes077.kernelChart.space =
        BinarySelectedAxis8T9.selectedAugmentation :=
      BinarySelectedCatalogue16T1098.module_eq
    _ = BinarySelectedAxis8T18.selectedAugmentation := by
      ext a
      rw [BinarySelectedAxis8T9.mem_selectedAugmentation_iff,
        BinarySelectedAxis8T18.mem_selectedAugmentation_iff]
      rfl

theorem original_eq_physical_split :
    Original=physicalFrame.splitAffineAction := by
  apply physicalFrame.eq_splitAffineAction_of_generators generators generators_full
  intro j
  rw [kernel_space,BinaryKernelAxes077.kernelChart.mem_iff]
  revert j
  unfold BinaryPairFrame.affineTranslation BinaryPairFrame.offset
  simp only [physicalFrame,generators,
    BinaryPairFrame.ofGenerators_top_generator]
  decide +kernel

theorem physical_split_eq_canonical :
    relabelSubgroup
        (physicalFrame.frame.symm.trans (binaryCoordinateRelabel labelRelabel))
        physicalFrame.splitAffineAction=
      binaryCoordinateSplitAction BinarySelectedAxis8T18.Action
        BinarySelectedAxis8T18.selectedAugmentation := by
  rw [← relabelSubgroup_trans,
    physicalFrame.relabelSubgroup_frame_symm_splitAffineAction,
    relabelSubgroup_binaryCoordinateSplitAction,top_eq,module_eq]

theorem physical_original_eq_canonical :
    relabelSubgroup
        (physicalFrame.frame.symm.trans (binaryCoordinateRelabel labelRelabel))
        Original=
      binaryCoordinateSplitAction BinarySelectedAxis8T18.Action
        BinarySelectedAxis8T18.selectedAugmentation := by
  calc
    relabelSubgroup
        (physicalFrame.frame.symm.trans (binaryCoordinateRelabel labelRelabel))
        Original =
        relabelSubgroup
          (physicalFrame.frame.symm.trans (binaryCoordinateRelabel labelRelabel))
          physicalFrame.splitAffineAction :=
      congrArg (relabelSubgroup
        (physicalFrame.frame.symm.trans (binaryCoordinateRelabel labelRelabel)))
        original_eq_physical_split
    _ = _ := physical_split_eq_canonical

end SymmetricSubgroupAsymptotics.BinarySelectedCatalogue16T1332
