import SymmetricSubgroupAsymptotics.BinaryHeadThreeCriticalTopUniformSeven
import SymmetricSubgroupAsymptotics.BinaryPairInnerSmallHeadUniformGenerators
import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenJointZeroFrames
import SymmetricSubgroupAsymptotics.AbelianKernelOrdinaryGeneration
import SymmetricSubgroupAsymptotics.BinaryInvariantCyclicGeneratorBound

/-! The original rank-nine degree-thirty-two action with actual top rank
at least six has uniform natural-module width seven. The five possible
actual inner kernels are handled by their retained original actions;
only the two width-four kernels need the sparse leading-label argument. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16))

private theorem head_three_ordinary_rank_le_kernel_add_top :
    MarkedC4.genRank U ≤ MarkedC4.normalGen F.top.ker + MarkedC4.genRank F.top.range := by
  letI : IsMulCommutative F.top.ker := ⟨⟨fun a b => F.bitsHom_injective (by
    rw [map_mul, map_mul, mul_comm])⟩⟩
  letI : IsMulCommutative F.top.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    infer_instance
  have hb := AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen
    F.top.rangeRestrict F.top.rangeRestrict_surjective
  rw [MonoidHom.ker_rangeRestrict] at hb
  omega

theorem uniform_generatedBy_seven_of_rank_nine_rank_six_top
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hhigh : 9 ≤ MarkedC4.genRank U) (hTopHigh : 6 ≤ MarkedC4.genRank F.top.range) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) 7 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : MulAction.IsPretransitive F.top.range (Fin 16) := F.top_pretransitive
  have hTop := F.top_isPGroup hU
  letI : Group.IsNilpotent F.top.range := hTop.isNilpotent
  have ht := twoGroup_transitive_normalGen_le_quarter_add_two F.top.range hTop
    (⊤ : Subgroup F.top.range)
  norm_num only [Nat.card_fin] at ht
  have htgen := (MarkedC4.genRank_le_normalGen_top (G := F.top.range)).trans ht
  have hg := F.head_three_ordinary_rank_le_kernel_add_top
  have hhead : 3 ≤ Module.finrank (ZMod 2)
      ((F.axisNaturalSubrepresentation F.top.ker).toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) F.top.range (ZMod 2))) := by
    rw [representationHead_finrank_eq_coinvariants, ← F.axisNatural_normalGen F.top.ker le_rfl hU]
    omega
  obtain ⟨E₀⟩ := transitiveBinaryPairFrame_nonempty 3 F.top.range hTop
    (by norm_num only [Nat.card_fin])
  rcases E₀.six_le_genRank_literal_top_models hTop hTopHigh with
    ⟨g, hH, hlarge⟩ | ⟨g, hH, hlarge⟩
  · let E := E₀.reindex g
    change 3 ≤ MarkedC4.normalGen E.top.ker at hlarge
    rcases E.regular_large_axis_models hTop E.top.ker le_rfl hH (by omega) with
      ⟨hK, hR⟩ | ⟨hK, hR⟩
    · have hchart : E.kernelSpace = (BinaryRegularEightNaturalRegistry.charts 45).2.space := by
        have he := E.ambientAxis_kernel.symm.trans hK
        rw [← BinaryRegularEightNaturalRegistry.kernel45_space,
          BinaryRegularEightNaturalRegistry.states_space] at he
        exact he
      exact (F.uniform_generatedBy_six_of_inner_regular45 E hU hH hchart).mono (by decide)
    · have hk : E.kernelSpace = BinaryRegularEightSquareCarry.K46 :=
        E.ambientAxis_kernel.symm.trans hK
      obtain ⟨u, a, hu, hconj⟩ := E.regular46_joint_exists_zero_offset_model
        hTop hTopHigh hH hk hR
      have hgen : Subgroup.closure (Set.range fun i => E.top (u i)) = E.top.range := by
        rw [show (fun i => E.top (u i)) = BinaryMenuCayley8T3.generators from funext hu, ← hH]
      have hz := E.eq_reoriented_split_of_generated_conjugate u hgen a hconj
      apply F.uniform_generatedBy_seven_of_head_three_regular46 (E.reorient a) hz _ _ hhead
      · simpa only [reorient_top] using hH
      · simpa only [reorient_kernelSpace] using hk
  · let E := E₀.reindex g
    change 2 ≤ MarkedC4.normalGen E.top.ker at hlarge
    rcases E.heisenberg_large_axis_models hTop E.top.ker le_rfl hH (by omega) with
      ⟨hK, hR⟩ | ⟨hK, hR⟩ | ⟨hK, hR⟩
    · have hchart : E.kernelSpace = (BinaryHeisenbergEightNaturalHeads.charts 12).2.space := by
        have he := E.ambientAxis_kernel.symm.trans hK
        rw [← BinaryHeisenbergEightNaturalHeads.kernel12_space,
          BinaryHeisenbergEightNaturalHeads.states_space] at he
        exact he
      exact (F.uniform_generatedBy_four_of_inner_heisenberg12 E hU hH hchart).mono (by decide)
    · have hchart : E.kernelSpace = (BinaryHeisenbergEightNaturalHeads.charts 13).2.space := by
        have he := E.ambientAxis_kernel.symm.trans hK
        rw [← BinaryHeisenbergEightNaturalHeads.kernel13_space,
          BinaryHeisenbergEightNaturalHeads.states_space] at he
        exact he
      exact (F.uniform_generatedBy_six_of_inner_heisenberg13 E hU hH hchart).mono (by decide)
    · have hk : E.kernelSpace = BinaryHeisenbergEightSquareCarry.K14 :=
        E.ambientAxis_kernel.symm.trans hK
      obtain ⟨u, a, hu, hconj⟩ := E.heisenberg14_joint_exists_zero_offset_model
        hTop hTopHigh hH hk hR
      have hgen : Subgroup.closure (Set.range fun i => E.top (u i)) = E.top.range := by
        rw [show (fun i => E.top (u i)) = BinaryHeisenbergEightSquareCarry.originalSelected from funext hu,
          BinaryHeisenbergEightSquareCarry.selected_closure_eq_original, ← hH]
      have hz := E.eq_reoriented_split_of_generated_conjugate u hgen a hconj
      apply F.uniform_generatedBy_seven_of_head_three_heisenberg14 (E.reorient a) hz _ _ hhead
      · simpa only [reorient_top] using hH
      · simpa only [reorient_kernelSpace] using hk

end SymmetricSubgroupAsymptotics.BinaryPairFrame
