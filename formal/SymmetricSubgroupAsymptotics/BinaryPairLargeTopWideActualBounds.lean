import SymmetricSubgroupAsymptotics.BinaryEightLargeTopWideLayerProfiles
import SymmetricSubgroupAsymptotics.BinaryPairRankFiveKernelConstant
import SymmetricSubgroupAsymptotics.BinaryNonelementaryPermutationHead
import SymmetricSubgroupAsymptotics.BinaryPairRegularSubgroupKernel45Head
import SymmetricSubgroupAsymptotics.MarkedC4ActualGlobalMarkGeneratorRank

/-! Actual wide-module consequences for the original29 and31 inner tops.
The original sixteen-point source, flip kernel and module are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (E : BinaryPairFrame U (Fin 8))

private theorem literal_eight_head_cap_two (hU : IsPGroup 2 U)
    (H : Subgroup (Equiv.Perm (Fin 8))) (hH : E.top.range = H)
    (hnon : ¬ ∀ g : H, g ^ 2 = 1)
    (A : Subrepresentation ((binaryPermutationRepresentation 8).comp H.subtype)) :
    Module.finrank (ZMod 2) A.toRepresentation.Coinvariants ≤ 2 := by
  letI largeTopWideActual_literalTransitive : MulAction.IsPretransitive H (Fin 8) := by
    rw [← hH]
    exact E.top_pretransitive
  have hp : IsPGroup 2 H := by rw [← hH]; exact E.top_isPGroup hU
  have hh := twoGroup_faithful_permutationSubrepresentationHead_le_quarter hp hnon A
  rw [representationHead_finrank_eq_coinvariants] at hh
  simpa only [Nat.card_fin] using hh

private theorem twenty_nine_not_elementary :
    ¬ ∀ g : BinaryEightTop29CoordinateAction.H, g ^ 2 = 1 := by
  have hn : ∃ i : Fin 64, (BinaryEightTop29CoordinateAction.row i) ^ 2 ≠ 1 := by decide +kernel
  intro h
  obtain ⟨i, hi⟩ := hn
  exact hi (h _)

private theorem thirty_one_not_elementary :
    ¬ ∀ g : BinaryEightTop31CoordinateAction.H, g ^ 2 = 1 := by
  have hn : ∃ i : Fin 64, (BinaryEightTop31CoordinateAction.row i) ^ 2 ≠ 1 := by decide +kernel
  intro h
  obtain ⟨i, hi⟩ := hn
  exact hi (h _)

theorem naturalModuleHead_le_three_of_top_twenty_nine_rank_five
    (hU : IsPGroup 2 U) (hrank : 5 ≤ MarkedC4.genRank U)
    (hH : E.top.range = BinaryEightTop29CoordinateAction.H)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X)) :
    Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ 3 := by
  have hc := E.rank_five_kernelSpace_contains_one hU hrank
  exact E.naturalModuleHead_le_of_literal_pair_layer_bound
    BinaryEightTop29CoordinateAction.H hH E.kernelSpace rfl 3
    (BinaryEightTop29HighHeadKernel.pair_layer_bound_three E.kernelSpace hc
      (E.literal_eight_head_cap_two hU _ hH twenty_nine_not_elementary)) W

theorem naturalModule_finrank_le_ten_of_top_thirty_one_rank_five_head_four
    (hU : IsPGroup 2 U) (hrank : 5 ≤ MarkedC4.genRank U)
    (hH : E.top.range = BinaryEightTop31CoordinateAction.H)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hwide : 4 ≤ Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) :
    Module.finrank (ZMod 2) W.toSubmodule ≤ 10 := by
  have hc := E.rank_five_kernelSpace_contains_one hU hrank
  exact E.naturalModule_finrank_le_of_literal_pair_head_dimension_profile
    BinaryEightTop31CoordinateAction.H hH E.kernelSpace rfl 4 10
    (fun S L hp hh => (BinaryEightTop31HighHeadKernel.pair_layer_head_four_dimension_ten
      E.kernelSpace hc (E.literal_eight_head_cap_two hU _ hH thirty_one_not_elementary)
        S L hp hh).le) W hwide

theorem kernelSpace_eq_chart44_of_top_thirty_one_rank_five_head_four
    (hU : IsPGroup 2 U) (hrank : 5 ≤ MarkedC4.genRank U)
    (hH : E.top.range = BinaryEightTop31CoordinateAction.H)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hwide : 4 ≤ Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) :
    E.kernelSpace = BinaryRegularEightNaturalRegistry.chart44.space := by
  have hmodel : MarkedC4.genRank BinaryEightTop31CoordinateAction.H ≤ 3 := by
    let a := BinaryEightTop31CoordinateAction.generators
    let S : Finset BinaryEightTop31CoordinateAction.H := Finset.univ.image a
    have hs : (S : Set BinaryEightTop31CoordinateAction.H) = Set.range a := by
      ext x
      simp only [S, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    have hg : Subgroup.closure (S : Set BinaryEightTop31CoordinateAction.H) = ⊤ := by
      rw [hs]
      exact closureGenerators_full _
    exact (MarkedC4.genRank_le hg).trans (Finset.card_image_le.trans (by simp))
  have ht := MarkedC4.ActualGlobalMarkGeneratorRank.genRank_le_of_surjective
    (MulEquiv.subgroupCongr hH).symm.toMonoidHom (MulEquiv.subgroupCongr hH).symm.surjective
  have hg := E.genRank_le_actual_pair_kernel_add_top
  have hker : 2 ≤ MarkedC4.normalGen E.top.ker := by omega
  let K := E.literalTopAxis BinaryEightTop31CoordinateAction.H hH E.top.ker
  have hKS : K.toSubmodule = E.kernelSpace := by
    rw [E.literalTopAxis_space]
    apply le_antisymm (E.ambientAxis_le_kernelSpace E.top.ker)
    rintro v ⟨a, rfl⟩
    exact (E.bits_mem_ambientAxis E.top.ker a.toMul).mpr a.toMul.property
  have hk : 2 ≤ Module.finrank (ZMod 2) K.toRepresentation.Coinvariants := by
    rw [E.literalTopAxis_head, ← E.axis_normalGen_eq_coinvariants E.top.ker le_rfl hU]
    exact hker
  rcases BinaryEightTop31HighHeadKernel.high_head_space K (by omega) with hk | hk
  · exact hKS.symm.trans hk
  · have hb := E.naturalModuleHead_le_three_of_top_thirty_one_kernel45 hH (hKS.symm.trans hk) W
    omega

end SymmetricSubgroupAsymptotics.BinaryPairFrame
