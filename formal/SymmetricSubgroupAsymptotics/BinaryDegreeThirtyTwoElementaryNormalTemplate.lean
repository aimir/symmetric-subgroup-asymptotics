import SymmetricSubgroupAsymptotics.BinaryPairAxisNaturalModule
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoElementarySaturation
import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenElementaryZeroFrame
import SymmetricSubgroupAsymptotics.BinaryPairElementaryOriginalGraphRigidity

/-! The elementary-top alternative selects the literal phi-zero module
for the same original normal intersection, using the actual original zero
frame and the checked pointwise-product layer rigidity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance binaryDegreeThirtyTwoElementaryNormalTemplateFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16))

theorem elementary_rank_nine_normal_actual_zero_template
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hgen : MarkedC4.genRank U ≤ 9)
    (hel : BinarySquareActionStructure.SquaresActTrivially (G := F.top.range) (X := Fin 16))
    (N : Subgroup U) [N.Normal] (hproper : N ≠ ⊤) (hN : 9 ≤ MarkedC4.normalGen N) :
    ∃ E : BinaryPairFrame F.top.range (Fin 8), F.top.range = E.splitAffineAction ∧
      E.top.range = BinaryRegularEightNaturalRegistry.H ∧
      E.kernelSpace = (BinaryRegularEightNaturalRegistry.charts 23).2.space ∧
      (E.originalCoordinateSubrepresentation
        (F.axisNaturalSubrepresentation (N ⊓ F.top.ker))).toSubmodule =
          (BinaryElementary16GraphHeadRigidity.stateChart 0).space := by
  obtain ⟨_,hB,_,_,_,_⟩ := F.elementary_proper_normal_nine_saturation
    hU hgen hel N hproper hN
  letI : MulAction.IsPretransitive F.top.range (Fin 16) := F.top_pretransitive
  have hTop := F.top_isPGroup hU
  let W := F.axisNaturalSubrepresentation (N ⊓ F.top.ker)
  have hwide : 6 ≤ Module.finrank (ZMod 2) W.toRepresentation.Coinvariants := by
    rw [← F.axisNatural_normalGen (N ⊓ F.top.ker) inf_le_right hU,hB]
  obtain ⟨E₀⟩ := transitiveBinaryPairFrame_nonempty 3 F.top.range hTop
    (by norm_num only [Nat.card_fin])
  obtain ⟨E,hzero,hH,hK⟩ := E₀.exists_original_elementary_zero_frame hTop
    (BinarySquareActionStructure.squaresActTrivially_iff_pow_two.mp hel)
  exact ⟨E,hzero,hH,hK,E.elementary_original_zero_graph hzero hH hK W hwide⟩

end SymmetricSubgroupAsymptotics.BinaryPairFrame
