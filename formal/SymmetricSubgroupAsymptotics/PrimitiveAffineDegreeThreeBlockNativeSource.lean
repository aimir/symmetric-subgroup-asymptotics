import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeResidualAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeThreeBlockEasy
import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveNumericalInstances
import SymmetricSubgroupAsymptotics.Non2PreE7ExceptionalSmallRankTailBridge
import SymmetricSubgroupAsymptotics.Non2PreE7ComparatorAbelianTowerInstances

/-!
# Block-native sources for the exact local-S3 residual cells

The coarse operation which prepends a ternary elementary layer to an
independently estimated signed quotient is not sharp at the smallest odd
width: `evenWidth 9 = 8`, and capacity one already consumes more than the
margin left by a comparator of degree four or five.  The historical small-S3
arguments avoid that loss by retaining the actual block system and counting
the ternary restriction jointly with the binary sign/top quotient.

This file therefore dispatches only from the concrete source records already
used by the numerical catalogue: S3EXC, S3ISO, S3CENT, S3TWO, S3CYCL and
S3SYL.  The natural-S3 quotient of degree three is also retained as the sole
valid pointwise three-block row.  No ledger label is accepted by itself.

`DegreeThreeExactS3BlockNativeClassification` is the precise finite
correspondence still needed from the literal minimal block and affine profile.
It returns one of the concrete source records, including its complete-source
inequality and menu bounds.  Thus it cannot be inhabited merely by naming an
owner family.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The concrete, already numerical source alternatives occurring in the
exact natural-S3 exceptional cells.  Every constructor contains the actual
source theorem on the original action. -/
inductive DegreeThreeExactS3BlockNativeSource : Type 1
  | exceptional (source : PreE7S3ExceptionalSource w U)
  | isotype
      (source : ComparatorAbelianTowerCertificateSourceData .s3iso w U)
  | central
      (source : ComparatorAbelianTowerCertificateSourceData .s3cent w U)
  | twoSign (source : PreE7S3TwoSource w U)
  | cyclicTop (source : PreE7S3CyclicSource w U)
  | symmetricTop (source : PreE7S3SylowSource w U)
  | pointwiseThree
      (blocks_eq : Nat.card block.Points = 3)
      (model : DegreeThreeThreeBlockPointwiseModel block P)

namespace DegreeThreeExactS3BlockNativeSource

/-- Convert a concrete block-native source into the final source sum.  The
pointwise constructor is the checked degree-three comparator row; all other
constructors enter through their existing catalogue package. -/
noncomputable def source
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (D : DegreeThreeExactS3BlockNativeSource block P) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  cases D with
  | exceptional S => exact .inl S.toRankTailOwnerSource
  | isotype S =>
      exact .inl (.ordinary .s3iso (.comparator (by decide) S))
  | central S =>
      exact .inl (.ordinary .s3cent (.comparator (by decide) S))
  | twoSign S =>
      exact .inl (.ordinary .s3two
        (.small (PreE7S3LocalAdditiveSource.numericalData S)))
  | cyclicTop S =>
      exact .inl (.ordinary .s3cycl
        (.small (PreE7S3LocalAdditiveSource.numericalData S)))
  | symmetricTop S =>
      exact .inl (.ordinary .s3syl
        (.small (PreE7S3LocalAdditiveSource.numericalData S)))
  | pointwiseThree hs M =>
      exact DegreeThreeThreeBlockPointwiseModel.source
        (block := block) (P := P) hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm hr hs M

end DegreeThreeExactS3BlockNativeSource

/-- The smallest honest finite correspondence boundary for the exact local
natural-S3 residual lane.  Its output is a concrete source theorem, not an
owner label or an isomorphism-type name. -/
abbrev DegreeThreeExactS3BlockNativeClassification :=
  ∀ {w : ℕ} (U : PreE7NonPairActionClass w) (_hw : 5 ≤ w)
    (basePoint : Fin w)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre),
    ImprimitiveAffineResidualCapacityException
        (Nat.card block.Fibre) (Nat.card block.Points)
        (Nat.card block.Component) →
    Nat.card block.Fibre = 3 →
    (Nat.card block.Points = 3 ∨ Nat.card block.Points = 4 ∨
      Nat.card block.Points = 6 ∨ Nat.card block.Points = 12 ∨
      Nat.card block.Points = 18) →
    Nat.card block.Component = 6 →
    Nonempty (DegreeThreeExactS3BlockNativeSource block P)

/-- Turn the finite block-native correspondence into the exact-S3 endpoint
consumed by the already checked degree-three exhaustion. -/
noncomputable def degreeThreeExactS3ResidualSource_of_blockNative
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (classification : DegreeThreeExactS3BlockNativeClassification) :
    DegreeThreeExactS3ResidualSource := by
  intro w U hw basePoint block P hres hr hs hcomponent
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hr]; norm_num)
  exact DegreeThreeExactS3BlockNativeSource.source
    (block := block) (P := P)
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr
    (Classical.choice
      (classification U hw basePoint block P hres hr hs hcomponent))

/-- Final degree-three residual source after the regular-six numerical row
and the finite exact-S3 block-native correspondence have been supplied. -/
noncomputable def degreeThreeResidualSource_of_blockNative
    (hKP : KovacsPraegerAbelianizationBound)
    (publishedSix : PublishedDegreeSixThreeByTwoAffineClassification)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (regularSix : DegreeThreeRegularSixResidualSource)
    (classification : DegreeThreeExactS3BlockNativeClassification) :
    PrimitiveAffineResidualDegreeSource 3 :=
  degreeThreeResidualSource_of_endpoints hKP publishedSix regularSix
    (degreeThreeExactS3ResidualSource_of_blockNative hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm classification)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
