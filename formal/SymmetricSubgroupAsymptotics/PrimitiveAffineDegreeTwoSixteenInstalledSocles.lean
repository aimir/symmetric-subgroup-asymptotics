import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow13FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow6FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow17FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenOneFrameNaturalBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow1QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow2QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow3QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow4QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow5QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow6QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow14FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow15FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow16FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow18FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow19FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow1QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow2FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow5FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow11QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow2AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow9FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow7FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow6FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow4FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow3FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow5AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow8AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow10AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow11FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow20FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow12FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow13FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow14FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow15FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow16AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow17AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow18AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow19AffineSocles

/-!
# Insert proved original quotient-socle families into the one-frame catalogue

The natural-module theorem is already uniform over all sixty-four actions.
The remaining data below supplies only the quotient-socle families outside
the exact installed positions. No completed position or natural-module
bound is requested again, and no missing quotient-socle family is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoSixteenInstalledSocles

open DegreeTwoSixteenPairFiniteCatalogue

def installedZero : Finset (Fin 29) := {0, 1, 2, 3, 4, 5, 13, 14, 15, 16, 17, 18}

def installedTwoAffine : Finset (Fin 15) := {0, 1, 4, 5, 10, 12}

def installedPrimitive : Finset (Fin 20) := Finset.univ

structure RemainingData : Type 1 where
  zero16 : ∀ j : Fin 29, j ∉ installedZero →
    (catalogue.zero16 j).normalRegistry.QuotientSocleGeneratorFamily 2
  twoAffine16 : ∀ j : Fin 15, j ∉ installedTwoAffine →
    (catalogue.twoAffine16 j).normalRegistry.QuotientSocleGeneratorFamily 2

namespace RemainingData

noncomputable def zeroFamily (D : RemainingData) (j : Fin 29) :
    (catalogue.zero16 j).normalRegistry.QuotientSocleGeneratorFamily 2 := by
  by_cases h0 : j = 0
  · subst j; exact PrimitiveAffineDegreeTwoZeroSixteenRow1QuotientSocles.family
  by_cases h1 : j = 1
  · subst j; exact PrimitiveAffineDegreeTwoZeroSixteenRow2QuotientSocles.family
  by_cases h2 : j = 2
  · subst j; exact PrimitiveAffineDegreeTwoZeroSixteenRow3QuotientSocles.family
  by_cases h3 : j = 3
  · subst j; exact PrimitiveAffineDegreeTwoZeroSixteenRow4QuotientSocles.family
  by_cases h4 : j = 4
  · subst j; exact PrimitiveAffineDegreeTwoZeroSixteenRow5QuotientSocles.family
  by_cases h5 : j = 5
  · subst j; exact PrimitiveAffineDegreeTwoZeroSixteenRow6QuotientSocles.family
  by_cases h13 : j = 13
  · subst j; exact PrimitiveAffineDegreeTwoZeroSixteenRow14QuotientSocles.family
  by_cases h14 : j = 14
  · subst j; exact PrimitiveAffineDegreeTwoZeroSixteenRow15QuotientSocles.family
  by_cases h17 : j = 17
  · subst j; exact PrimitiveAffineDegreeTwoZeroSixteenRow18QuotientSocles.family
  by_cases h18 : j = 18
  · subst j; exact PrimitiveAffineDegreeTwoZeroSixteenRow19QuotientSocles.family
  by_cases h15 : j = 15
  · subst j; exact PrimitiveAffineDegreeTwoZeroSixteenRow16QuotientSocles.family
  by_cases h16 : j = 16
  · subst j; exact PrimitiveAffineDegreeTwoZeroSixteenRow17QuotientSocles.family
  exact D.zero16 j (by simp [installedZero, h0, h1, h2, h3, h4, h5, h13, h14, h15, h16, h17, h18])

noncomputable def twoAffineFamily (D : RemainingData) (j : Fin 15) :
    (catalogue.twoAffine16 j).normalRegistry.QuotientSocleGeneratorFamily 2 := by
  by_cases h0 : j = 0
  · subst j; exact PrimitiveAffineDegreeTwoTwoAffineSixteenRow1QuotientSocles.family
  by_cases h4 : j = 4
  · subst j; exact PrimitiveAffineDegreeTwoTwoAffineSixteenRow5QuotientSocles.family
  by_cases h10 : j = 10
  · subst j; exact PrimitiveAffineDegreeTwoTwoAffineSixteenRow11QuotientSocles.family
  by_cases h1 : j = 1
  · subst j; exact PrimitiveAffineDegreeTwoTwoAffineSixteenRow2QuotientSocles.family
  by_cases h5 : j = 5
  · subst j; exact PrimitiveAffineDegreeTwoTwoAffineSixteenRow6QuotientSocles.family
  by_cases h12 : j = 12
  · subst j; exact PrimitiveAffineDegreeTwoTwoAffineSixteenRow13QuotientSocles.family
  exact D.twoAffine16 j (by simp [installedTwoAffine, h0, h1, h4, h5, h10, h12])

noncomputable def primitiveFamily (j : Fin 20) :
    (catalogue.primitive16 j).normalRegistry.QuotientSocleGeneratorFamily 2 := by
  by_cases h0 : j = 0
  · subst j; exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.family
  by_cases h1 : j = 1
  · subst j; exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow2AffineSocles.family
  by_cases h4 : j = 4
  · subst j; exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow5AffineSocles.family
  by_cases h7 : j = 7
  · subst j; exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow8AffineSocles.family
  by_cases h9 : j = 9
  · subst j; exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow10AffineSocles.family
  by_cases h11 : j = 11
  · subst j; exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow12AffineSocles.family
  by_cases h12 : j = 12
  · subst j; exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow13AffineSocles.family
  by_cases h13 : j = 13
  · subst j; exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow14AffineSocles.family
  by_cases h14 : j = 14
  · subst j; exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow15AffineSocles.family
  by_cases h15 : j = 15
  · subst j; exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow16AffineSocles.family
  by_cases h16 : j = 16
  · subst j; exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow17AffineSocles.family
  by_cases h17 : j = 17
  · subst j; exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow18AffineSocles.family
  by_cases h18 : j = 18
  · subst j; exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow19AffineSocles.family
  by_cases h2 : j = 2
  · subst j; exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow3AffineSocles.family
  by_cases h3 : j = 3
  · subst j; exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow4AffineSocles.family
  by_cases h5 : j = 5
  · subst j; exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow6AffineSocles.family
  by_cases h6 : j = 6
  · subst j; exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow7AffineSocles.family
  by_cases h8 : j = 8
  · subst j; exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow9AffineSocles.family
  by_cases h10 : j = 10
  · subst j; exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow11AffineSocles.family
  by_cases h19 : j = 19
  · subst j; exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow20AffineSocles.family
  exfalso
  fin_cases j <;> contradiction

/-- Assemble all original one-frame packages once precisely the remaining
quotient-socle families are supplied. -/
noncomputable def finiteCatalogue (D : RemainingData) :
    DegreeTwoSixteenOneFrameFiniteRows.Catalogue.DegreeTwoSixteenOneFrameFiniteCatalogueData :=
  PrimitiveAffineDegreeTwoSixteenOneFrameNaturalBounds.ofSocleFamilies
    D.zeroFamily D.twoAffineFamily primitiveFamily

end RemainingData
end DegreeTwoSixteenInstalledSocles
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
