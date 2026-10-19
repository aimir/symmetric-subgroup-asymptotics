import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairSourceCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopCatalogues

/-! Source-facing degree-two assembly. Only the count-six input changes
from a legacy owner record to the exact representative source consumed by
the proof. The complete residual menu and all other endpoints are identical.
No existing interface or installed assembly is modified. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoSourceResidualAssembly

/-- Bind the actual minimal block to its exact six-pair representative. -/
def sixPairSource (source : DegreeTwoSixPairRepresentativeB6Source)
    (U : PreE7NonPairActionClass 12) (basePoint : Fin 12)
    (block : OriginalMinimalBlock (A := preE7NonPairAction 12 U) basePoint)
    (hFibre : Nat.card block.Fibre = 2) (hPoints : Nat.card block.Points = 6) :
    PreE7RankTailSourceOrYonedaTopData 12 U := by
  let F : BinaryPairFrame (preE7NonPairAction 12 U) (Fin 6) :=
    (OriginalMinimalBlock.pairFrameOfFibreCardTwo
      (A := preE7NonPairAction 12 U) block hFibre).reindex
        (Finite.equivFinOfCardEq hPoints)
  let p : PreE7PairActionClass 6 := ⟨U.1,⟨F⟩⟩
  have hUp : preE7SixPairNonPairAction p = U := Subtype.ext rfl
  rw [← hUp]
  exact .inl (.b6 (source p))

/-- The original exhaustive residual proof with an exact source on every
actual six-pair representative. No literal normal registry is consumed. -/
def source_of_endpoints
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (publishedThree : PublishedDegreeTwoThreePairRepresentativeClassification)
    (publishedFour : PublishedDegreeTwoFourPairClassification)
    (sixPair : DegreeTwoSixPairRepresentativeB6Source)
    (eightPair : DegreeTwoEightPairResidualSource)
    (twelvePair : DegreeTwoTwelvePairResidualSource)
    (sixteenPair : DegreeTwoSixteenPairResidualSource) :
    PrimitiveAffineResidualDegreeSource 2 := by
  intro w U hw basePoint block P hres hr
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hr]; norm_num)
  refine Classical.choice ?_
  cases hcap : hres.toCapacityException with
  | degreeThree hr' hs => omega
  | degreeFour hr' hs => omega
  | degreeFive hr' hs => omega
  | degreeEight hr' hs => omega
  | degreeNine hr' hs => omega
  | degreeSixteen hr' hs => omega
  | degreeTwo hr' hs =>
      rcases ComponentSource.degreeTwoException_small block hw hr hs with
        hs3 | hs4 | hs6 | hs8 | hs12 | hs16
      · have hw6 : w = 6 := by simpa only [hr,hs3] using width_eq block
        subst w
        exact ⟨degreeTwoThreePairSource_of_representative publishedThree
          U basePoint block hr hs3⟩
      · have hw8 : w = 8 := by simpa only [hr,hs4] using width_eq block
        subst w
        exact ⟨degreeTwoFourPairSource hZmud lit publishedFour U basePoint block hr hs4⟩
      · have hw12 : w = 12 := by simpa only [hr,hs6] using width_eq block
        subst w
        exact ⟨sixPairSource sixPair U basePoint block hr hs6⟩
      · exact ⟨eightPair U hw basePoint block P hres hr hs8⟩
      · exact ⟨twelvePair U hw basePoint block P hres hr hs12⟩
      · exact ⟨sixteenPair U hw basePoint block P hres hr hs16⟩

/-- Actual182source construction and actual coverage still both required. -/
def source_of_sourceTable
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (publishedThree : PublishedDegreeTwoThreePairRepresentativeClassification)
    (publishedFour : PublishedDegreeTwoFourPairClassification)
    (sixPair : PrimitiveAffineDegreeTwoSixPairSourceTable)
    (publishedSix : PublishedDegreeTwoSixPairSourceCatalogueLocator sixPair)
    (eightPair : DegreeTwoEightPairResidualSource)
    (twelvePair : DegreeTwoTwelvePairResidualSource)
    (sixteenPair : DegreeTwoSixteenPairResidualSource) :
    PrimitiveAffineResidualDegreeSource 2 :=
  source_of_endpoints hZmud lit publishedThree publishedFour
    (degreeTwoSixPairSource_of_sourceTable sixPair publishedSix) eightPair twelvePair sixteenPair

/-- Minimal catalogue assembly variant: all other literal catalogues and
semantic resolutions remain exact and mandatory. Its result is the unchanged
final affine consumer input PrimitiveAffineResidualDegreeSource2. -/
def source_of_catalogues
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (publishedThree : PublishedDegreeTwoThreePairRepresentativeClassification)
    (publishedFour : PublishedDegreeTwoFourPairClassification)
    (sixPair : PrimitiveAffineDegreeTwoSixPairSourceTable)
    (publishedSix : PublishedDegreeTwoSixPairSourceCatalogueLocator sixPair)
    (eight : DegreeTwoEightPairFiniteCatalogue)
    (publishedEight : PublishedDegreeTwoEightPairCatalogueLocator eight)
    (twelve : DegreeTwoTwelvePairTopFiniteCatalogue)
    (publishedTwelve : PublishedDegreeTwoTwelvePairTopCatalogueLocator twelve)
    (resolveTwelve : DegreeTwoTwelvePairTopCatalogueResolution twelve)
    (sixteen : DegreeTwoSixteenPairTopFiniteCatalogue)
    (publishedSixteen : PublishedDegreeTwoSixteenPairTopCatalogueLocator sixteen)
    (resolveSixteen : DegreeTwoSixteenPairTopCatalogueResolution sixteen) :
    PrimitiveAffineResidualDegreeSource 2 :=
  source_of_sourceTable hZmud lit publishedThree publishedFour sixPair publishedSix
    (degreeTwoEightPairResidualSource_of_catalogue eight publishedEight)
    (degreeTwoTwelvePairResidualSource_of_catalogue twelve publishedTwelve resolveTwelve)
    (degreeTwoSixteenPairResidualSource_of_catalogue sixteen publishedSixteen resolveSixteen)

end DegreeTwoSourceResidualAssembly
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
end
