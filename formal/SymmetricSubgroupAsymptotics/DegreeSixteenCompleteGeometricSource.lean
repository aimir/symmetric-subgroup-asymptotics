import SymmetricSubgroupAsymptotics.WidthThirtyTwoCompleteQuartetSource
import SymmetricSubgroupAsymptotics.DegreeSixteenGeometricSourceAssembly
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockProductFrame

/-! Exhaustive actual sixteen-point top geometry supplies the complete
original thirty-two-point pair source. No incomplete finite sixteen-point
locator, per-row source certificate or module estimate is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.DegreeSixteenCompleteGeometricSource
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open BinaryPlanePermutationAffineEquiv

def quartetSource
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    DegreeSixteenGeometricSourceAssembly.QuartetSource := by
  intro p F _ _ point D hf hi
  let e : Plane ≃ Fin 4 :=
    Finite.equivFinOfCardEq (by simp [Plane, Nat.card_eq_fintype_card])
  let C := D.productFrame (Finite.equivFinOfCardEq hi)
    ((Finite.equivFinOfCardEq hf).trans e.symm)
  exact WidthThirtyTwoCompleteQuartetSource.source p F C published8 hZmud lit

def representativeSource
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    DegreeTwoSixteenPairRepresentativeSource :=
  DegreeSixteenGeometricSourceAssembly.representativeSource_of_quartetSource
    published8 published16 socle hMN hZmud lit (quartetSource published8 hZmud lit)

def residualSource
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    DegreeTwoSixteenPairResidualSource :=
  degreeTwoSixteenPairResidualSource_of_representative
    (representativeSource published8 published16 socle hMN hZmud lit)

end SymmetricSubgroupAsymptotics.DegreeSixteenCompleteGeometricSource
