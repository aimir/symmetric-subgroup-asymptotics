import SymmetricSubgroupAsymptotics.BinaryCommonEightFullConstantGenerators
import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenJointZeroFrames
import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenElementaryZeroFrame
import SymmetricSubgroupAsymptotics.BinaryPairOriginalGraphRigidity
import SymmetricSubgroupAsymptotics.BinaryPairElementaryOriginalGraphRigidity
import SymmetricSubgroupAsymptotics.BinaryHeisenbergEightNaturalCarrySpaces
import SymmetricSubgroupAsymptotics.BinaryNonelementaryPermutationHead

/-! A rank-ten original degree-thirty-two source has natural-module
width at most six. The checked joint sixteen-point frontier supplies the
actual inner zero frame; the common pointwise shears handle arbitrary
outer lift offsets. No outer-carry certificate is used here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16))

private theorem ordinary_rank_le_kernel_add_top :
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

include F in
theorem uniform_generatedBy_six_of_rank_ten
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hhigh : 10 ≤ MarkedC4.genRank U) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) 6 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : MulAction.IsPretransitive F.top.range (Fin 16) := F.top_pretransitive
  have hTop := F.top_isPGroup hU
  letI : Group.IsNilpotent F.top.range := hTop.isNilpotent
  let W := F.axisNaturalSubrepresentation F.top.ker
  have hker : MarkedC4.normalGen F.top.ker =
      Module.finrank (ZMod 2) W.toRepresentation.Coinvariants :=
    F.axisNatural_normalGen F.top.ker le_rfl hU
  have hgen := F.ordinary_rank_le_kernel_add_top
  obtain ⟨E₀⟩ := transitiveBinaryPairFrame_nonempty 3 F.top.range hTop
    (by norm_num only [Nat.card_fin])
  by_cases hpow : ∀ t : F.top.range, t ^ 2 = 1
  · have hel : BinarySquareActionStructure.SquaresActTrivially
        (G := F.top.range) (X := Fin 16) :=
      BinarySquareActionStructure.squaresActTrivially_iff_pow_two.mpr hpow
    have ht := ElementaryBinaryTransitiveNormalRank.normalGen_le_exponent
      hel (0 : Fin 16) 4 (by norm_num only [Nat.card_fin] : Nat.card (Fin 16) = 2 ^ 4) (⊤ : Subgroup F.top.range)
    have htgen := (MarkedC4.genRank_le_normalGen_top (G := F.top.range)).trans ht
    have hwide : 6 ≤ Module.finrank (ZMod 2) W.toRepresentation.Coinvariants := by omega
    obtain ⟨E, hzero, hH, hK⟩ := E₀.exists_original_elementary_zero_frame hTop hpow
    have hW := E.elementary_original_zero_graph hzero hH hK W hwide
    exact F.uniform_generatedBy_six_of_elementary_zero_kernel E hzero hH hK hW
  · have hb := twoGroup_faithful_permutationSubrepresentationHead_le_quarter hTop hpow W
    rw [representationHead_finrank_eq_coinvariants] at hb
    norm_num only [Nat.card_fin] at hb
    have ht := twoGroup_transitive_normalGen_le_quarter_add_two F.top.range hTop
      (⊤ : Subgroup F.top.range)
    norm_num only [Nat.card_fin] at ht
    have htgen := (MarkedC4.genRank_le_normalGen_top (G := F.top.range)).trans ht
    have htopHigh : 6 ≤ MarkedC4.genRank F.top.range := by omega
    have hwide : 4 ≤ Module.finrank (ZMod 2) W.toRepresentation.Coinvariants := by omega
    obtain ⟨E, hzero, hmodels⟩ := E₀.exists_joint_zero_frame hTop htopHigh W hwide
    rcases hmodels with ⟨hH, hK, _⟩ | ⟨hH, hK, _⟩
    · have hKchart : E.kernelSpace = (BinaryRegularEightNaturalRegistry.charts 46).2.space := by
        rw [← BinaryRegularEightNaturalRegistry.states_space,
          BinaryRegularEightNaturalRegistry.kernel46_space]
        exact hK
      rcases E.regular46_four_le_head_forces_original_layers hH hKchart W hwide with
        ⟨hS, hL⟩ | ⟨hS, hL⟩
      · have hW := E.regular_parity_original_zero_graph hzero hH hK W hS hL hwide
        exact F.uniform_generatedBy_six_of_regular_zero_kernel E hzero hH hK hW
      · exact F.uniform_generatedBy_six_of_regular_full_constant_kernel E hzero hH hK hS hL
    · have hKchart : E.kernelSpace = (BinaryHeisenbergEightNaturalHeads.charts 14).2.space := by
        rw [← BinaryHeisenbergEightNaturalHeads.states_space,
          BinaryHeisenbergEightNaturalHeads.kernel14_space]
        exact hK
      obtain ⟨hS, hL⟩ := E.heisenberg14_four_le_head_forces_original_layers hH hKchart W hwide
      have hW := E.heisenberg_parity_original_zero_graph hzero hH hK W hS hL hwide
      exact F.uniform_generatedBy_six_of_heisenberg_zero_kernel E hzero hH hK hW

end SymmetricSubgroupAsymptotics.BinaryPairFrame
