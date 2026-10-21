import SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T22Kernel14
import SymmetricSubgroupAsymptotics.BinaryPairWideOriginalLayers
import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerDimension

/-! Existing actual kernel-product denominator certificates exclude the
apparent dimension-twelve borderline. A head-three original state of
dimension at least twelve has the same upper chart33 and full lower layer.
Only a scalar comparison of the already certified71 layer pairs is added. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryHeisenbergFourteenHighLayers
open BinaryHeisenbergEightNaturalHeads
open BinaryPairLayerHead8T22Kernel14
private theorem high_dimension_three_indices : ∀ p : Fin 71,
    12≤(charts (sourceIndex p)).1+(charts (targetIndex p)).1 →
    (charts (denominatorIndex p)).1+3≤headCeiling (sourceIndex p)+(charts (targetIndex p)).1 →
    sourceIndex p=13 ∧ targetIndex p=1 := by decide +kernel

theorem high_dimension_three_head_forces_layers (S L : Subrepresentation rho)
    (hproduct : binaryCoordinateProductSpan (charts 14).2.space S.toSubmodule≤L.toSubmodule)
    (hlarge : 12≤Module.finrank (ZMod 2) S.toSubmodule+Module.finrank (ZMod 2) L.toSubmodule)
    (hhead : 3≤Module.finrank (ZMod 2) S.toRepresentation.Coinvariants+
      Module.finrank (ZMod 2) (L.toSubmodule ⧸
        ((binaryCoordinateProductSpan (charts 14).2.space S.toSubmodule).comap L.toSubmodule.subtype ⊔
          Representation.Coinvariants.ker L.toRepresentation))) :
    S=states 13 ∧ L=states 1 := by
  obtain ⟨i,rfl⟩ := complete S
  obtain ⟨j,rfl⟩ := complete L
  have hc : compatible i j := by
    intro a b
    have ha : (charts 14).2.inclusion (Pi.single a 1)∈(charts 14).2.space := ⟨_,rfl⟩
    have hb : (charts i).2.inclusion (Pi.single b 1)∈(states i).toSubmodule := by
      rw [states_space]
      exact ⟨_,rfl⟩
    exact hproduct (binaryCoordinateProductSpan.product_mem _ _ _ ha _ hb)
  obtain ⟨p,hi,hj⟩ := covered i j hc
  subst i
  subst j
  have hd := denominator_dimension_le p hproduct
  have hh := coinvariants_finrank_le (sourceIndex p)
  have hnum : (charts (denominatorIndex p)).1+3≤
      headCeiling (sourceIndex p)+(charts (targetIndex p)).1 := by omega
  have hsize : 12≤(charts (sourceIndex p)).1+(charts (targetIndex p)).1 := by
    simpa only [states_space,BinaryCoordinateSpace.finrank] using hlarge
  obtain ⟨hs,hl⟩ := high_dimension_three_indices p hsize hnum
  exact ⟨congrArg states hs,congrArg states hl⟩
end SymmetricSubgroupAsymptotics.BinaryHeisenbergFourteenHighLayers

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (E : BinaryPairFrame U (Fin 8))
include E

theorem heisenberg14_large_head_three_original_layers
    (hH : E.top.range=BinaryHeisenbergEightNaturalHeads.H)
    (hJ : E.kernelSpace=(BinaryHeisenbergEightNaturalHeads.charts 14).2.space)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hlarge : 12≤Module.finrank (ZMod 2) W.toSubmodule)
    (hhead : 3≤Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) :
    (E.pairSumModuleLayer W).toSubmodule=BinaryRegularEightNaturalRegistry.chart33.space ∧
      (E.pairConstantModuleLayer W).toSubmodule=⊤ := by
  let S := E.literalPairLayer BinaryHeisenbergEightNaturalHeads.H hH (E.pairSumModuleLayer W)
  let L := E.literalPairLayer BinaryHeisenbergEightNaturalHeads.H hH (E.pairConstantModuleLayer W)
  have hp : binaryCoordinateProductSpan (BinaryHeisenbergEightNaturalHeads.charts 14).2.space
      S.toSubmodule≤L.toSubmodule := by
    have hp := E.actual_kernel_pairSum_product_le_constantLayer W
    rw [hJ] at hp
    simpa only [S,L,E.literalPairLayer_space] using hp
  have hb := hhead.trans (E.pairModuleHead_le_literalLayers _ hH W)
  rw [hJ] at hb
  have hsize : 12≤Module.finrank (ZMod 2) S.toSubmodule+Module.finrank (ZMod 2) L.toSubmodule := by
    have hd := E.pairModuleLayers_finrank W
    rw [hd] at hlarge
    have hs : S.toSubmodule=(E.pairSumModuleLayer W).toSubmodule :=
      E.literalPairLayer_space _ hH _
    have hl : L.toSubmodule=(E.pairConstantModuleLayer W).toSubmodule :=
      E.literalPairLayer_space _ hH _
    have hsd : Module.finrank (ZMod 2) S.toSubmodule=
        Module.finrank (ZMod 2) (E.pairSumModuleLayer W).toSubmodule :=
      congrArg (fun P : Submodule (ZMod 2) (Fin 8 → ZMod 2) => Module.finrank (ZMod 2) P) hs
    have hld : Module.finrank (ZMod 2) L.toSubmodule=
        Module.finrank (ZMod 2) (E.pairConstantModuleLayer W).toSubmodule :=
      congrArg (fun P : Submodule (ZMod 2) (Fin 8 → ZMod 2) => Module.finrank (ZMod 2) P) hl
    rw [hsd,hld]
    exact hlarge
  obtain ⟨hs,hl⟩ := BinaryHeisenbergFourteenHighLayers.high_dimension_three_head_forces_layers S L hp hsize hb
  constructor
  · simpa only [S,E.literalPairLayer_space,BinaryHeisenbergEightNaturalHeads.states_space] using
      congrArg Subrepresentation.toSubmodule hs
  · have hspace : (E.pairConstantModuleLayer W).toSubmodule=BinaryRegularEightNaturalRegistry.chart1.space := by
      simpa only [L,E.literalPairLayer_space,BinaryHeisenbergEightNaturalHeads.states_space] using
        congrArg Subrepresentation.toSubmodule hl
    rw [hspace]
    apply Submodule.eq_top_of_finrank_eq
    rw [BinaryRegularEightNaturalRegistry.chart1.finrank]
    simp
end SymmetricSubgroupAsymptotics.BinaryPairFrame
