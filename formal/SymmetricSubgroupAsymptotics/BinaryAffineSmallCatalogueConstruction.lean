import SymmetricSubgroupAsymptotics.BinaryAffineSmallCatalogueData
import SymmetricSubgroupAsymptotics.SmallAffineCanonicalFixedFacts
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenComplementLocator
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightCanonicalComplements

/-! Construct the abstract binary-affine package only after its independent
literal degree16 carriers have been built. The consumer interface has no
reverse dependency on this finite construction. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.BinaryAffineSmallCatalogueData

/-- The only retained classification is the already-used actual primitive16
correspondence. The binary8 branch and all representative facts are proved. -/
def ofPrimitiveSixteen
    (published : PrimitiveSixteenCanonicalCatalogue.PublishedClassification) :
    BinaryAffineSmallCatalogueData where
  representative := SmallAffineCanonicalRepresentatives.representative
  representativeFacts r := {
    card_eq := (SmallAffineCanonicalFixedFacts.proved r).card_eq
    solvable_iff := (SmallAffineCanonicalFixedFacts.proved r).solvable_iff
    nonsolubleCore := (SmallAffineCanonicalFixedFacts.proved r).nonsolubleCore }
  locate := by
    intro G X _ _ _ _ _ hp P x h
    rcases h with h8 | h16
    · letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by rw [h8]; decide)
      exact PrimitiveAffineDegreeEightCanonicalComplements.catalogue_locator P hp x h8
    · exact PrimitiveAffineSixteenComplementLocator.catalogue_locator published hp P x h16


end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.BinaryAffineSmallCatalogueData
