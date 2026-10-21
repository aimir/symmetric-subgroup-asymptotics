import SymmetricSubgroupAsymptotics.BinaryPairScalarGraphCharts
import SymmetricSubgroupAsymptotics.BinaryPairWideOriginalLayers
import SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T3Kernel23
import SymmetricSubgroupAsymptotics.BinaryElementary16GraphHeadRigidity

/-! The original elementary-sixteen frontier has just sixteen scalar
forms. Exact original layer dimensions and literal source rows force its
zero graph, without an elementary-sixteen invariant-subspace census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

namespace BinaryElementary16GraphHeadRigidity

def sumChart : BinaryCoordinateSpace 8 4 := (BinaryRegularEightNaturalRegistry.charts 46).2

def coefficientForm (p : Fin 16) : Fin 4 → ZMod 2 := binaryVectorOfMask 4 p.val

theorem coefficientForm_surjective : Function.Surjective coefficientForm := by
  unfold Function.Surjective coefficientForm
  decide +kernel

private theorem graph_basis : ∀ p j,
    (BinaryPairFrame.pairLayerFlatten.symm ((stateChart p).inclusion (Pi.single j 1))).2 ∈ sumChart.space ∧
    binaryEightParity
      (BinaryPairFrame.pairLayerFlatten.symm ((stateChart p).inclusion (Pi.single j 1))).1 =
      ∑ i, sumChart.coordinates
        (BinaryPairFrame.pairLayerFlatten.symm ((stateChart p).inclusion (Pi.single j 1))).2 i *
          coefficientForm p i := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem generatorTop_original : ∀ i, generatorTop i = 1 ∨
    ∃ j : Fin 3, generatorTop i = BinaryMenuCayley8T3.generators j := by decide +kernel

private theorem generatorOffset_kernel : ∀ i,
    generatorOffset i ∈ (BinaryRegularEightNaturalRegistry.charts 23).2.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel

end BinaryElementary16GraphHeadRigidity

namespace BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8))

theorem elementary_six_le_head_forces_original_layers
    (hH : F.top.range = BinaryRegularEightNaturalRegistry.H)
    (hK : F.kernelSpace = (BinaryRegularEightNaturalRegistry.charts 23).2.space)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hwide : 6 ≤ Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) :
    (F.pairSumModuleLayer W).toSubmodule = (BinaryRegularEightNaturalRegistry.charts 46).2.space ∧
      (F.pairConstantModuleLayer W).toSubmodule = (BinaryRegularEightNaturalRegistry.charts 45).2.space := by
  let S := F.literalPairLayer BinaryRegularEightNaturalRegistry.H hH (F.pairSumModuleLayer W)
  let L := F.literalPairLayer BinaryRegularEightNaturalRegistry.H hH (F.pairConstantModuleLayer W)
  have hp : binaryCoordinateProductSpan (BinaryRegularEightNaturalRegistry.charts 23).2.space
      S.toSubmodule ≤ L.toSubmodule := by
    have hp := F.actual_kernel_pairSum_product_le_constantLayer W
    rw [hK] at hp
    simpa only [S,L,F.literalPairLayer_space] using hp
  have hb := hwide.trans (F.pairModuleHead_le_literalLayers _ hH W)
  rw [hK] at hb
  obtain ⟨hs,hl⟩ := BinaryPairLayerHead8T3Kernel23.six_le_pair_head_forces_layers S L hp hb
  constructor
  · simpa only [S,F.literalPairLayer_space,BinaryRegularEightNaturalRegistry.states_space] using
      congrArg Subrepresentation.toSubmodule hs
  · simpa only [L,F.literalPairLayer_space,BinaryRegularEightNaturalRegistry.states_space] using
      congrArg Subrepresentation.toSubmodule hl

theorem elementary_parity_layers_exists_original_graph_chart
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hS : (F.pairSumModuleLayer W).toSubmodule = (BinaryRegularEightNaturalRegistry.charts 46).2.space)
    (hL : (F.pairConstantModuleLayer W).toSubmodule = (BinaryRegularEightNaturalRegistry.charts 45).2.space) :
    ∃ p : Fin 16, (F.originalCoordinateSubrepresentation W).toSubmodule =
      (BinaryElementary16GraphHeadRigidity.stateChart p).space := by
  have hL' := hL.trans regular45_eq_parity_kernel
  obtain ⟨c,hgraph⟩ := F.exists_pairModule_graph_coefficients W
    BinaryElementary16GraphHeadRigidity.sumChart hS binaryEightParity hL'
  obtain ⟨p,hp⟩ := BinaryElementary16GraphHeadRigidity.coefficientForm_surjective c
  refine ⟨p,F.originalCoordinateSubrepresentation_eq_chart W _ ?_ ?_⟩
  · rw [hS,hL]
    have hs := (BinaryRegularEightNaturalRegistry.charts 46).2.finrank
    have hl := (BinaryRegularEightNaturalRegistry.charts 45).2.finrank
    change Module.finrank (ZMod 2) (BinaryRegularEightNaturalRegistry.charts 46).2.space +
      Module.finrank (ZMod 2) (BinaryRegularEightNaturalRegistry.charts 45).2.space = 11
    rw [hs,hl]
    change 4 + 7 = 11
    decide
  · intro j
    rw [hgraph]
    simp only [pairSum_originalCoordinateEquiv_symm,pairZero_originalCoordinateEquiv_symm,← hp]
    exact BinaryElementary16GraphHeadRigidity.graph_basis p j

/-- All rows are constructed in the actual original zero source. -/
theorem elementary_original_zero_graph
    (hzero : U = F.splitAffineAction)
    (hH : F.top.range = BinaryRegularEightNaturalRegistry.H)
    (hK : F.kernelSpace = (BinaryRegularEightNaturalRegistry.charts 23).2.space)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hwide : 6 ≤ Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) :
    (F.originalCoordinateSubrepresentation W).toSubmodule =
      (BinaryElementary16GraphHeadRigidity.stateChart 0).space := by
  obtain ⟨hS,hL⟩ := F.elementary_six_le_head_forces_original_layers hH hK W hwide
  obtain ⟨p,hp⟩ := F.elementary_parity_layers_exists_original_graph_chart W hS hL
  have ht (i : Fin 4) : BinaryElementary16GraphHeadRigidity.generatorTop i ∈ F.top.range := by
    rcases BinaryElementary16GraphHeadRigidity.generatorTop_original i with hi | ⟨j,hi⟩
    · rw [hi]
      exact F.top.range.one_mem
    · rw [hi,hH]
      exact Subgroup.subset_closure ⟨j,rfl⟩
  have ha (i : Fin 4) : BinaryElementary16GraphHeadRigidity.generatorOffset i ∈ F.kernelSpace := by
    rw [hK]
    exact BinaryElementary16GraphHeadRigidity.generatorOffset_kernel i
  let u : Fin 4 → U := fun i => F.originalZeroRow hzero
    ⟨BinaryElementary16GraphHeadRigidity.generatorTop i,ht i⟩
    (BinaryElementary16GraphHeadRigidity.generatorOffset i) (ha i)
  have hact (i : Fin 4) : F.originalCoordinateRepresentation (u i) =
      BinaryElementary16GraphHeadRigidity.action i :=
    F.originalCoordinateRepresentation_zeroRow hzero
      ⟨BinaryElementary16GraphHeadRigidity.generatorTop i,ht i⟩ _ (ha i)
  have hhead : 6 ≤ Module.finrank (ZMod 2)
      (F.originalCoordinateSubrepresentation W).toRepresentation.Coinvariants := by
    rwa [← F.originalCoordinateSubrepresentation_head W]
  have he := BinaryElementary16GraphHeadRigidity.form_eq_zero_of_large_head
    F.originalCoordinateRepresentation u (F.originalCoordinateSubrepresentation W) p hp hact hhead
  simpa only [he] using hp

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
