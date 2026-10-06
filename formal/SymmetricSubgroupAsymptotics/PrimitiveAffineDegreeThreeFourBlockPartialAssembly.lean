import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeNonzeroPartialAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockNonbinaryClosure

/-!
# Remove the nonbinary four-block cell from the degree-three residual

The literal signed quotient at four blocks is either binary or nonbinary.
The nonbinary half is now discharged by the published four-pair catalogue
and the correlated ternary prepend.  This file leaves the binary four-block
cell visible, with its actual block system and nonzero pair kernel, and
exposes only block counts six, twelve and eighteen beyond it.

Both residual types below are construction boundaries.  They are not
assumptions intended to survive the final affine consumer.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- The remaining binary four-block signed quotient, retaining the literal
pair chart and the proof that its pair kernel is nonzero. -/
abbrev DegreeThreeFourBlockBinaryResidualSource :=
  ∀ {w : ℕ} (U : PreE7NonPairActionClass w) (_hw : 5 ≤ w)
    (basePoint : Fin w)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre],
    ImprimitiveAffineResidualCapacityException
        (Nat.card block.Fibre) (Nat.card block.Points)
        (Nat.card block.Component) →
    (hr : Nat.card block.Fibre = 3) →
    (hs : Nat.card block.Points = 4) →
    (hcomponent : Nat.card block.Component = 6) →
    degreeNineLinearBlockKernel block P ≠ ⊥ →
    IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action →
    PreE7RankTailSourceOrYonedaTopData w U

/-- Construction boundary after every four-block cell has been removed. -/
abbrev DegreeThreeNonzeroSignedKernelPostFourResidualSource :=
  ∀ {w : ℕ} (U : PreE7NonPairActionClass w) (_hw : 5 ≤ w)
    (basePoint : Fin w)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre),
    ImprimitiveAffineResidualCapacityException
        (Nat.card block.Fibre) (Nat.card block.Points)
        (Nat.card block.Component) →
    Nat.card block.Fibre = 3 →
    (Nat.card block.Points = 6 ∨ Nat.card block.Points = 12 ∨
      Nat.card block.Points = 18) →
    Nat.card block.Component = 6 →
    degreeNineLinearBlockKernel block P ≠ ⊥ →
    PreE7RankTailSourceOrYonedaTopData w U

/-- Insert the checked nonbinary four-block row.  The binary half remains
separate because the ten-row nonbinary pair catalogue does not apply to it. -/
noncomputable def degreeThreeNonzeroSignedKernelLaterSource_of_postFour
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hgen : PermutationSubgroupGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (published : PublishedDegreeTwoFourPairClassification)
    (binaryFour : DegreeThreeFourBlockBinaryResidualSource)
    (postFour : DegreeThreeNonzeroSignedKernelPostFourResidualSource) :
    DegreeThreeNonzeroSignedKernelLaterResidualSource := by
  intro w U hw basePoint block P hres hr hs hcomponent hK
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hr]; norm_num)
  by_cases hs4 : Nat.card block.Points = 4
  · let C := degreeThreeFourBlockPairChart block P hr hs4 hcomponent
    by_cases hbinary : IsPGroup 2 C.action
    · exact binaryFour U hw basePoint block P hres hr hs4 hcomponent hK hbinary
    · exact degreeThreeFourBlockNonbinarySource block P hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm hgen hZmud lit published hr hs4 hcomponent
          hbinary
  by_cases hs6 : Nat.card block.Points = 6
  · exact postFour U hw basePoint block P hres hr (Or.inl hs6) hcomponent hK
  by_cases hs12 : Nat.card block.Points = 12
  · exact postFour U hw basePoint block P hres hr
      (Or.inr (Or.inl hs12)) hcomponent hK
  have hs18 : Nat.card block.Points = 18 := by
    rcases hs with h | h | h | h
    · exact False.elim (hs4 h)
    · exact False.elim (hs6 h)
    · exact False.elim (hs12 h)
    · exact h
  exact postFour U hw basePoint block P hres hr
    (Or.inr (Or.inr hs18)) hcomponent hK

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
