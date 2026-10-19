import SymmetricSubgroupAsymptotics.SmallAffineCanonicalReceipt
import SymmetricSubgroupAsymptotics.DegreeTwentyFiveActualProjectiveData

/-! Construct the finite affine package from bare published classifications
and ordinary group theorems. The full representative receipt, actual
degree-25 scalar quotient, and every-chief composition bound are internal
conclusions, never arguments of this constructor. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

def PublishedPrimitiveAffineFiniteLiterature.ofCanonicalClassifications
    (catalogue : SmallAffineCanonicalRepresentatives.PublishedClassification)
    (simple : StandardThreeDimensionalLinearGroups.PublishedSimplicity)
    (burnside : PublishedBurnsideTwoPrimeSolvabilityInput)
    (projective : StandardGLTwoFiveProjective.PublishedProjectiveIsomorphism)
    (halasiMaroti : HalasiMarotiSolubleIrreducibleCubeBound)
    (degreeFive : PublishedDegreeFiveAffineClassification) :
    PublishedPrimitiveAffineFiniteLiterature where
  smallCatalogue := {
    locator := SmallAffineCanonicalRepresentatives.locator catalogue
    representativeFacts :=
      SmallAffineCanonicalRepresentatives.receipt catalogue simple burnside }
  degreeTwentyFive := DegreeTwentyFiveActualProjectiveData.publishedDegreeTwentyFiveLinearData burnside projective
  halasiMaroti := halasiMaroti
  degreeFive := degreeFive

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
