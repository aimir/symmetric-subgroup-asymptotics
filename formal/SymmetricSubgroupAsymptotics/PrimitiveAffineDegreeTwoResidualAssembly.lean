import SymmetricSubgroupAsymptotics.PrimitiveAffineFinalPartialAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveDegreeTwoOwnerReduction
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoThreePairsRawPackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourPairsClassification
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairCatalogueDispatcher

/-!
# Assembly of the degree-two affine residual lane

The numerical exhaustion and the literal pair-frame exclusions leave exactly
six block counts: three, four, six, eight, twelve, and sixteen.  The first two
are already handled by the published small-pair classifications.  The
six-block case is the checked 182-row B6 catalogue; this file supplies its
missing block-to-representative adapter.

The only remaining finite construction boundaries are therefore the
representative-level eight-, twelve-, and sixteen-pair sources below.  A
single adapter transports any such representative source back to the actual
minimal block.  This keeps block reindexing out of the finite importers and
prevents three copies of the same proof.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- The remaining eight-pair block-facing source constructor. -/
abbrev DegreeTwoEightPairResidualSource :=
  ∀ {w : ℕ} (U : PreE7NonPairActionClass w) (_hw : 5 ≤ w)
    (basePoint : Fin w)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre),
    ImprimitiveAffineResidualCapacityException
        (Nat.card block.Fibre) (Nat.card block.Points)
        (Nat.card block.Component) →
    Nat.card block.Fibre = 2 →
    Nat.card block.Points = 8 →
    PreE7RankTailSourceOrYonedaTopData w U

/-- The remaining twelve-pair block-facing source constructor. -/
abbrev DegreeTwoTwelvePairResidualSource :=
  ∀ {w : ℕ} (U : PreE7NonPairActionClass w) (_hw : 5 ≤ w)
    (basePoint : Fin w)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre),
    ImprimitiveAffineResidualCapacityException
        (Nat.card block.Fibre) (Nat.card block.Points)
        (Nat.card block.Component) →
    Nat.card block.Fibre = 2 →
    Nat.card block.Points = 12 →
    PreE7RankTailSourceOrYonedaTopData w U

/-- The remaining sixteen-pair block-facing source constructor. -/
abbrev DegreeTwoSixteenPairResidualSource :=
  ∀ {w : ℕ} (U : PreE7NonPairActionClass w) (_hw : 5 ≤ w)
    (basePoint : Fin w)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre),
    ImprimitiveAffineResidualCapacityException
        (Nat.card block.Fibre) (Nat.card block.Points)
        (Nat.card block.Component) →
    Nat.card block.Fibre = 2 →
    Nat.card block.Points = 16 →
    PreE7RankTailSourceOrYonedaTopData w U

/-! ## Common representative adapter -/

/-- A pair action with fewer than twenty-four pairs canonically belongs to
the non-pair residual action index.  That index only excludes the four
residual pair counts `384, 768, 1536, 3072`; the selected pre-`E7` exclusion
is already carried by the underlying `PreE7PairActionClass`.

The proof argument is retained explicitly so the same construction can be
used for all small pair counts without introducing a new finite action
index. -/
def preE7SmallPairNonPairAction
    (s : ℕ) (hs : s < 24) (p : PreE7PairActionClass s) :
    PreE7NonPairActionClass (2 * s) :=
  ⟨p.1, fun d hdegree _hframe => by
    have hcount : d.pairCount = s := by omega
    have hlarge := d.pairCount_ge_24
    omega⟩

@[simp] theorem preE7SmallPairNonPairAction_literal
    (s : ℕ) (hs : s < 24) (p : PreE7PairActionClass s) :
    preE7NonPairAction (2 * s) (preE7SmallPairNonPairAction s hs p) =
      preE7PairAction s p :=
  rfl

/-- Finite importers work at a fixed pair representative.  The common
adapter below turns this into the block-facing endpoint used by the affine
residual dispatcher. -/
abbrev DegreeTwoPairRepresentativeSource (s : ℕ) (hs : s < 24) :=
  ∀ p : PreE7PairActionClass s,
    PreE7RankTailSourceOrYonedaTopData (2 * s)
      (preE7SmallPairNonPairAction s hs p)

abbrev DegreeTwoEightPairRepresentativeSource :=
  DegreeTwoPairRepresentativeSource 8 (by norm_num)

abbrev DegreeTwoTwelvePairRepresentativeSource :=
  DegreeTwoPairRepresentativeSource 12 (by norm_num)

abbrev DegreeTwoSixteenPairRepresentativeSource :=
  DegreeTwoPairRepresentativeSource 16 (by norm_num)

/-- Reindex the literal pair frame supplied by an actual two-point minimal
block and dispatch it through a representative-level finite source. -/
noncomputable def degreeTwoSmallPairSource_of_representative
    {s : ℕ} (hs : s < 24)
    (source : DegreeTwoPairRepresentativeSource s hs)
    (U : PreE7NonPairActionClass (2 * s))
    (basePoint : Fin (2 * s))
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction (2 * s) U) basePoint)
    (hFibre : Nat.card block.Fibre = 2)
    (hPoints : Nat.card block.Points = s) :
    PreE7RankTailSourceOrYonedaTopData (2 * s) U := by
  let F : BinaryPairFrame (preE7NonPairAction (2 * s) U) (Fin s) :=
    (OriginalMinimalBlock.pairFrameOfFibreCardTwo
      (A := preE7NonPairAction (2 * s) U) block hFibre).reindex
        (Finite.equivFinOfCardEq hPoints)
  let p : PreE7PairActionClass s := ⟨U.1, ⟨F⟩⟩
  have hUp : preE7SmallPairNonPairAction s hs p = U := Subtype.ext rfl
  rw [← hUp]
  exact source p

/-- The representative-level eight-pair catalogue supplies the exact
block-facing endpoint. -/
noncomputable def degreeTwoEightPairResidualSource_of_representative
    (source : DegreeTwoEightPairRepresentativeSource) :
    DegreeTwoEightPairResidualSource := by
  intro w U _hw basePoint block _P _hres hFibre hPoints
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hwidth : w = 16 := by
    simpa only [hFibre, hPoints] using width_eq block
  subst w
  exact degreeTwoSmallPairSource_of_representative (s := 8) (by norm_num)
    source U basePoint block hFibre hPoints

/-- The representative-level twelve-pair catalogue supplies the exact
block-facing endpoint. -/
noncomputable def degreeTwoTwelvePairResidualSource_of_representative
    (source : DegreeTwoTwelvePairRepresentativeSource) :
    DegreeTwoTwelvePairResidualSource := by
  intro w U _hw basePoint block _P _hres hFibre hPoints
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hwidth : w = 24 := by
    simpa only [hFibre, hPoints] using width_eq block
  subst w
  exact degreeTwoSmallPairSource_of_representative (s := 12) (by norm_num)
    source U basePoint block hFibre hPoints

/-- The representative-level sixteen-pair catalogue supplies the exact
block-facing endpoint. -/
noncomputable def degreeTwoSixteenPairResidualSource_of_representative
    (source : DegreeTwoSixteenPairRepresentativeSource) :
    DegreeTwoSixteenPairResidualSource := by
  intro w U _hw basePoint block _P _hres hFibre hPoints
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hwidth : w = 32 := by
    simpa only [hFibre, hPoints] using width_eq block
  subst w
  exact degreeTwoSmallPairSource_of_representative (s := 16) (by norm_num)
    source U basePoint block hFibre hPoints

/-- Bind the six-pair frame supplied by an actual minimal block to the
representative-level 182-row B6 dispatcher. -/
noncomputable def degreeTwoSixPairSource_of_table
    (table : PrimitiveAffineDegreeTwoSixPairOwnerTable)
    (published : PublishedDegreeTwoSixPairCatalogueLocator table)
    (U : PreE7NonPairActionClass 12)
    (basePoint : Fin 12)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction 12 U) basePoint)
    (hFibre : Nat.card block.Fibre = 2)
    (hPoints : Nat.card block.Points = 6) :
    PreE7RankTailSourceOrYonedaTopData 12 U := by
  let F : BinaryPairFrame (preE7NonPairAction 12 U) (Fin 6) :=
    (OriginalMinimalBlock.pairFrameOfFibreCardTwo
      (A := preE7NonPairAction 12 U) block hFibre).reindex
        (Finite.equivFinOfCardEq hPoints)
  let p : PreE7PairActionClass 6 := ⟨U.1, ⟨F⟩⟩
  have hUp : preE7SixPairNonPairAction p = U := Subtype.ext rfl
  rw [← hUp]
  exact .inl (.b6 (degreeTwoSixPairSource table published p))

/-- Exhaust the complete degree-two residual menu.  Counts three and four
use the existing published representative classifications, count six uses
the checked B6 table, and only counts eight, twelve, and sixteen remain as
block-facing finite construction boundaries. -/
noncomputable def degreeTwoResidualSource_of_endpoints
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (publishedThree : PublishedDegreeTwoThreePairRepresentativeClassification)
    (publishedFour : PublishedDegreeTwoFourPairClassification)
    (sixPairTable : PrimitiveAffineDegreeTwoSixPairOwnerTable)
    (publishedSix : PublishedDegreeTwoSixPairCatalogueLocator sixPairTable)
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
      · have hw6 : w = 6 := by
          simpa only [hr, hs3] using width_eq block
        subst w
        exact ⟨degreeTwoThreePairSource_of_representative publishedThree
          U basePoint block hr hs3⟩
      · have hw8 : w = 8 := by
          simpa only [hr, hs4] using width_eq block
        subst w
        exact ⟨degreeTwoFourPairSource hZmud lit publishedFour U basePoint
          block hr hs4⟩
      · have hw12 : w = 12 := by
          simpa only [hr, hs6] using width_eq block
        subst w
        exact ⟨degreeTwoSixPairSource_of_table sixPairTable publishedSix U
          basePoint block hr hs6⟩
      · exact ⟨eightPair U hw basePoint block P hres hr hs8⟩
      · exact ⟨twelvePair U hw basePoint block P hres hr hs12⟩
      · exact ⟨sixteenPair U hw basePoint block P hres hr hs16⟩

/-- Assemble the complete degree-two residual source from the three
representative-level finite catalogues.  All block-facing transport is
provided by `degreeTwoSmallPairSource_of_representative`. -/
noncomputable def degreeTwoResidualSource_of_representatives
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (publishedThree : PublishedDegreeTwoThreePairRepresentativeClassification)
    (publishedFour : PublishedDegreeTwoFourPairClassification)
    (sixPairTable : PrimitiveAffineDegreeTwoSixPairOwnerTable)
    (publishedSix : PublishedDegreeTwoSixPairCatalogueLocator sixPairTable)
    (eightPair : DegreeTwoEightPairRepresentativeSource)
    (twelvePair : DegreeTwoTwelvePairRepresentativeSource)
    (sixteenPair : DegreeTwoSixteenPairRepresentativeSource) :
    PrimitiveAffineResidualDegreeSource 2 :=
  degreeTwoResidualSource_of_endpoints hZmud lit publishedThree
    publishedFour sixPairTable publishedSix
    (degreeTwoEightPairResidualSource_of_representative eightPair)
    (degreeTwoTwelvePairResidualSource_of_representative twelvePair)
    (degreeTwoSixteenPairResidualSource_of_representative sixteenPair)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
