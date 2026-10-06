import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockPartialAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockDiagonalSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockDiagonalOrder
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockDistinctSignSource
import SymmetricSubgroupAsymptotics.Non2PreE7ExceptionalSmallRankTailBridge

/-!
# Final sign-isotype dispatcher for the binary four-block cell

The literal sign partition has one, two, or four classes.  The four-class
source is constructed from the action itself.  The other two constructors
ask only for their finite structural comparison certificates; all source
exponents, coefficient aggregation, padding and menu estimates have already
been proved in the corresponding source modules.

This file returns the exact `DegreeThreeFourBlockBinaryResidualSource`
required by the degree-three residual assembly.  The obsolete universal
pointed-marker embedding is neither imported nor assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- Finite diagonal-model correspondence on the actual literal action.
The action-order bound is proved from the diagonal pair kernel and is not a
field of this input. -/
abbrev DegreeThreeFourBlockDiagonalComparisonSource :=
  ∀ {w : ℕ} (U : PreE7NonPairActionClass w)
    (basePoint : Fin w)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (_hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action),
    (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 1 →
      DegreeNineCentralProductModel
        (preE7NonPairAction w U ⧸ E block P)

/-- Finite two-sign normal-stratum correspondence on the actual action. -/
abbrev DegreeThreeFourBlockTwoSignComparisonSource :=
  ∀ {w : ℕ} (U : PreE7NonPairActionClass w)
    (basePoint : Fin w)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (_hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action),
    (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2 →
      DegreeThreeFourBlockTwoSignComparison block P

/-- Select the exact complete source belonging to the literal sign-isotype
count.  The one- and two-sign branches both use the complete-source S3EXC
interface, which keeps their already correlated all-normal inequalities and
avoids an additional ambient normal-axis factor. -/
noncomputable def degreeThreeFourBlockBinarySource_of_signedComparisons
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (diagonal : DegreeThreeFourBlockDiagonalComparisonSource)
    (twoSign : DegreeThreeFourBlockTwoSignComparisonSource) :
    DegreeThreeFourBlockBinaryResidualSource := by
  intro w U _hw basePoint block P _hNT _hres hr hs hcomponent _hK hbinary
  let C := degreeThreeFourBlockSignedIsotypeProfile
    block P hr hs hcomponent
  if h₁ : C.isotypeCount = 1 then
    let M := diagonal U basePoint block P hr hs hcomponent hbinary h₁
    let horder := degreeThreeFourBlock_diagonalSignedQuotient_card_le
      block P hr hs hcomponent h₁
    let S := degreeThreeFourBlock_diagonalExceptionalSource block P
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hs
      M horder
    exact .inl S.toRankTailOwnerSource
  else if h₂ : C.isotypeCount = 2 then
    let D := twoSign U basePoint block P hr hs hcomponent hbinary h₂
    let S := D.exceptionalSource block P hr hs
    exact .inl S.toRankTailOwnerSource
  else
    have h₄ : C.isotypeCount = 4 :=
      (C.cases.resolve_left h₁).resolve_left h₂
    let S := degreeThreeFourBlock_distinctSignExceptionalSource
      block P hr hs hcomponent hbinary h₄
    exact .inl S.toRankTailOwnerSource

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
