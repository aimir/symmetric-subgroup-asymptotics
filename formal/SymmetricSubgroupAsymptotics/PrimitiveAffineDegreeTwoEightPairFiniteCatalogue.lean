import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFiniteNormalImporter
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoResidualAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairSummedSource

/-!
# Degree-two eight-pair finite catalogue target

`nonbinary_actions.json` contains 527 degree-sixteen actions: 518 mixed
character rows, two quotient-comparator rows, and seven correlated head
rows.  This file is the Lean table shape for exactly that partition.

Mixed and comparator rows pass through the finite normal-state importer.
Head rows retain their source-summed exceptional term and enter through the
existing `PreE7DegreeTwoPairSummedSource` boundary.  Consequently every
constructor produces the final `PreE7RankTailSourceOrYonedaTopData` required
by the affine residual lane; no historical family label is accepted as a
proof.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- The non-pair index attached to an eight-pair representative. -/
abbrev degreeTwoEightPairNonPairAction
    (p : PreE7PairActionClass 8) : PreE7NonPairActionClass 16 :=
  preE7SmallPairNonPairAction 8 (by norm_num) p

/-- One semantically checked row of the 527-action degree-sixteen table. -/
inductive DegreeTwoEightPairImportedRow
    (p : PreE7PairActionClass 8) : Type 1 where
  /-- One of the 518 rows whose every proper quotient carries a mixed
  character tuple. -/
  | mixed
      (data : PreE7FiniteMixedCharacterMenuData 16
        (degreeTwoEightPairNonPairAction p))
  /-- One of the two rows whose interval above a distinguished normal
  subgroup is paid by a faithful degree-eight quotient action. -/
  | comparator
      (data : PreE7FiniteQcharMenuData 16
        (degreeTwoEightPairNonPairAction p))
  /-- A correlated head row after its cold and hot sums have been combined
  into one numerical margin. -/
  | correlated
      (source : PreE7DegreeTwoPairSummedSource 16
        (degreeTwoEightPairNonPairAction p))
      (margin : source.NumericalMargin)
  /-- A correlated head row retaining distinct main and cold slopes. -/
  | correlatedAdditive
      (source : PreE7DegreeTwoPairSummedSource 16
        (degreeTwoEightPairNonPairAction p))
      (margin : source.AdditiveNumericalMargin)

namespace DegreeTwoEightPairImportedRow

variable {p : PreE7PairActionClass 8}
  (R : DegreeTwoEightPairImportedRow p)

/-- Every imported row lands directly at the final source-or-Yoneda
boundary consumed by the degree-two residual assembly. -/
noncomputable def source :
    PreE7RankTailSourceOrYonedaTopData 16
      (degreeTwoEightPairNonPairAction p) :=
  match R with
  | .mixed data => data.rankTailSource
  | .comparator data => data.rankTailSource
  | .correlated source margin => .inr (.inr (source.toResidualChoice margin))
  | .correlatedAdditive source margin =>
      .inr (.inr (source.toResidualChoiceAdditive margin))

end DegreeTwoEightPairImportedRow

/-- The fully populated table has one semantic row for each of the 527
nonbinary degree-sixteen catalogue actions. -/
structure DegreeTwoEightPairFiniteCatalogue where
  representative : Fin 527 → PreE7PairActionClass 8
  row : ∀ j, DegreeTwoEightPairImportedRow (representative j)

/-- Published transitive-group catalogue locator restricted to nonbinary
degree-sixteen actions with eight two-point blocks.  This is exactly the
Hulpke small-transitive-group classification as distributed in TransGrp
3.6.5 (`Hulpke2005`, `TransGrp365` in the paper bibliography).  It is
deliberately separate from the independently checked semantic rows. -/
def PublishedDegreeTwoEightPairCatalogueLocator
    (T : DegreeTwoEightPairFiniteCatalogue) : Prop :=
  ∀ p : PreE7PairActionClass 8, ∃ j : Fin 527, p = T.representative j

/-- Dispatch the checked 527-row table on an arbitrary eight-pair
representative. -/
noncomputable def degreeTwoEightPairRepresentativeSource_of_catalogue
    (T : DegreeTwoEightPairFiniteCatalogue)
    (published : PublishedDegreeTwoEightPairCatalogueLocator T) :
    DegreeTwoEightPairRepresentativeSource := by
  intro p
  obtain ⟨j, rfl⟩ := published p
  exact (T.row j).source

/-- The same table supplies the block-facing residual endpoint. -/
noncomputable def degreeTwoEightPairResidualSource_of_catalogue
    (T : DegreeTwoEightPairFiniteCatalogue)
    (published : PublishedDegreeTwoEightPairCatalogueLocator T) :
    DegreeTwoEightPairResidualSource :=
  degreeTwoEightPairResidualSource_of_representative
    (degreeTwoEightPairRepresentativeSource_of_catalogue T published)

/-- Assemble the degree-two residual lane with the eight-pair endpoint
discharged by the semantic 527-row table.  Only the independent count-12
and count-16 pair-top endpoints remain as arguments. -/
noncomputable def degreeTwoResidualSource_of_eightPairCatalogue
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (publishedThree : PublishedDegreeTwoThreePairRepresentativeClassification)
    (publishedFour : PublishedDegreeTwoFourPairClassification)
    (sixPairTable : PrimitiveAffineDegreeTwoSixPairOwnerTable)
    (publishedSix : PublishedDegreeTwoSixPairCatalogueLocator sixPairTable)
    (eightPairTable : DegreeTwoEightPairFiniteCatalogue)
    (publishedEight :
      PublishedDegreeTwoEightPairCatalogueLocator eightPairTable)
    (twelvePair : DegreeTwoTwelvePairResidualSource)
    (sixteenPair : DegreeTwoSixteenPairResidualSource) :
    PrimitiveAffineResidualDegreeSource 2 :=
  degreeTwoResidualSource_of_endpoints hZmud lit publishedThree
    publishedFour sixPairTable publishedSix
    (degreeTwoEightPairResidualSource_of_catalogue
      eightPairTable publishedEight)
    twelvePair sixteenPair

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
