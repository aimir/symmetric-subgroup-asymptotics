import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSourceResidualAssembly

/-! The exact six-pair residual endpoint accepts any already integrated
source/Yoneda alternative on the ACTUAL representative. This permits
source-summed and rank-tail certificates; no owner predicate, normal census,
or catalogue coverage is inferred from a label. The old B6 route embeds. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

abbrev DegreeTwoSixPairRepresentativeSource :=
  ∀ p : PreE7PairActionClass 6,
    PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p)

structure PrimitiveAffineDegreeTwoSixPairGeneralSourceTable where
  representative : Fin 182 → PreE7PairActionClass 6
  source : ∀ i,PreE7RankTailSourceOrYonedaTopData 12
    (preE7SixPairNonPairAction (representative i))

def degreeTwoSixPairGeneralSource_of_table
    (T : PrimitiveAffineDegreeTwoSixPairGeneralSourceTable)
    (coverage : ∀ p : PreE7PairActionClass 6,∃ i : Fin 182,p=T.representative i) :
    DegreeTwoSixPairRepresentativeSource := by
  intro p
  let i := Classical.choose (coverage p)
  have hi : p=T.representative i := Classical.choose_spec (coverage p)
  rw [hi]
  exact T.source i

def degreeTwoSixPairGeneralSource_of_B6 (source : DegreeTwoSixPairRepresentativeB6Source) :
    DegreeTwoSixPairRepresentativeSource := fun p => .inl (.b6 (source p))

namespace PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoGeneralSourceResidualAssembly

def sixPairSource (source : DegreeTwoSixPairRepresentativeSource)
    (U : PreE7NonPairActionClass 12) (basePoint : Fin 12)
    (block : OriginalMinimalBlock (A := preE7NonPairAction 12 U) basePoint)
    (hFibre : Nat.card block.Fibre=2) (hPoints : Nat.card block.Points=6) :
    PreE7RankTailSourceOrYonedaTopData 12 U := by
  let F : BinaryPairFrame (preE7NonPairAction 12 U) (Fin 6) :=
    (OriginalMinimalBlock.pairFrameOfFibreCardTwo
      (A := preE7NonPairAction 12 U) block hFibre).reindex (Finite.equivFinOfCardEq hPoints)
  let p : PreE7PairActionClass 6 := ⟨U.1,⟨F⟩⟩
  have hUp : preE7SixPairNonPairAction p=U := Subtype.ext rfl
  rw [←hUp]
  exact source p

def source_of_endpoints
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (publishedThree : PublishedDegreeTwoThreePairRepresentativeClassification)
    (publishedFour : PublishedDegreeTwoFourPairClassification)
    (sixPair : DegreeTwoSixPairRepresentativeSource)
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


end PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoGeneralSourceResidualAssembly
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
end
