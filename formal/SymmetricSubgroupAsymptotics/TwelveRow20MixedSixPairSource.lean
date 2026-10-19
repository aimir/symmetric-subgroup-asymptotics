import SymmetricSubgroupAsymptotics.DirectPrimeFactorCharacterAxes
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveDiagonalTernarySocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairGeneralSourceAssembly

/-! A real mixed-character source beyond the capacity-one subset: the
original row20 is an actual image of A4 × C3. Every ORIGINAL normal quotient
is supplied by the direct-prime-factor theorem, including diagonal normal
subgroups. The historical capacity-two label is not treated as capacity one. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelveRow20MixedSixPairSource
open Non2UnipotentPrefixFiniteMenu Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue PrimitiveAffineDegreeTwoTwelveDiagonalTernarySocles

abbrev C := TernaryFourDiagonalActions.C3

def modelMap : A4 × C →* Row20Top :=
  row20Map.comp TernaryFourDiagonalActions.productToModel

theorem modelMap_surjective : Function.Surjective modelMap :=
  row20Map_surjective.comp TernaryFourDiagonalActions.productToModel_surjective

/-- The displayed A4 factor has the required bound on all its own original
normal quotients, by its checked normal chain. -/
theorem factor_socle (M : Subgroup A4) [M.Normal] :
    SocleNormalGeneratorBound (A4 ⧸ M) 1 :=
  quotientSocleNormalGeneratorBound_one_of_normal_total
    NaturalFourNormalChains.alternating_normal_total M

/-- Exact representative-facing mixed source, through the SAME original
row20 quotient maps. No per-normal character or count is supplied. -/
def source (hZmud : ZmudFaithfulCharacterTupleInput)
    (p : PreE7PairActionClass 6) (e : Row20Top ≃* preE7PairAction 6 p) :
    PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p) := by
  have hc : Nat.card C=3 := by
    rw [Nat.card_congr Multiplicative.toAdd,Nat.card_zmod]
  letI : Fact (Nat.card C).Prime := ⟨by rw [hc]; decide⟩
  let rho : A4 × C →* preE7PairAction 6 p := e.toMonoidHom.comp modelMap
  have hrho : Function.Surjective rho := e.surjective.comp modelMap_surjective
  let axes : PreE7B6CharacterOnlyQuotientData (preE7PairAction 6 p) :=
    PreE7B6CharacterOnlyQuotientData.ofAxes hZmud (fun N => by
      letI : N.val.Normal := N.property
      exact DirectPrimeFactorCharacterAxes.axis_of_surjective C
        factor_socle rho hrho N.val)
  exact .inl (.b6 (axes.toB6ActionCertificate (preE7PairFrame 6 p)))

end SymmetricSubgroupAsymptotics.TwelveRow20MixedSixPairSource
