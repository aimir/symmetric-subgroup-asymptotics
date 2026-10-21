import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoRankNineElementaryTop
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoRankNineRankSixTop
import SymmetricSubgroupAsymptotics.BinaryPairHeadFourTriangularUniformSeven
import SymmetricSubgroupAsymptotics.TransitiveBinaryTriangularCoordinates
import SymmetricSubgroupAsymptotics.BinaryNonelementaryPermutationHead
import SymmetricSubgroupAsymptotics.AbelianKernelOrdinaryGeneration

/-! Every original rank-at-least-nine degree-thirty-two binary action
has natural-module width seven. The intermediate top-rank-five case uses
its actual triangular tower and original head-four axis, rather than an
assumed elementary subgroup or a replacement split action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16))

private theorem complete_rank_nine_ordinary_rank_le_kernel_add_top :
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
theorem uniform_generatedBy_seven_of_rank_nine
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hhigh : 9 ≤ MarkedC4.genRank U) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) 7 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : MulAction.IsPretransitive F.top.range (Fin 16) := F.top_pretransitive
  have hTop := F.top_isPGroup hU
  by_cases hpow : ∀ g : F.top.range, g ^ 2 = 1
  · exact F.uniform_generatedBy_seven_of_rank_nine_elementary_top hU hhigh hpow
  by_cases hlarge : 6 ≤ MarkedC4.genRank F.top.range
  · exact F.uniform_generatedBy_seven_of_rank_nine_rank_six_top hU hhigh hlarge
  have hnon : ¬BinarySquareActionStructure.SquaresActTrivially
      (G := F.top.range) (X := Fin 16) := by
    intro h
    exact hpow (BinarySquareActionStructure.squaresActTrivially_iff_pow_two.mp h)
  let W := F.axisNaturalSubrepresentation F.top.ker
  have hW := twoGroup_permutationSubrepresentationGeneratedBy_quarter_of_not_elementary hTop hnon W
  norm_num only [Nat.card_fin] at hW
  obtain ⟨v, hv⟩ := hW
  have hheadle := representationHead_finrank_le_generators W.toRepresentation v hv
  have hkernel : MarkedC4.normalGen F.top.ker =
      Module.finrank (ZMod 2) (W.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) F.top.range (ZMod 2))) := by
    rw [representationHead_finrank_eq_coinvariants]
    exact F.axisNatural_normalGen F.top.ker le_rfl hU
  have hgen := F.complete_rank_nine_ordinary_rank_le_kernel_add_top
  have hhead : Module.finrank (ZMod 2) (W.toRepresentation.IntertwiningMap
      (Representation.trivial (ZMod 2) F.top.range (ZMod 2))) = 4 := by omega
  obtain ⟨T⟩ := transitive_binary_triangular_coordinates_exists 4 F.top.range hTop
    (by norm_num only [Nat.card_fin])
  exact F.uniform_generatedBy_seven_of_nonelementary_triangular_axis_head_four T hTop hnon hhead

end SymmetricSubgroupAsymptotics.BinaryPairFrame
