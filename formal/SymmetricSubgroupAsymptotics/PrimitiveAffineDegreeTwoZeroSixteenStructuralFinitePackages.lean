import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenActualSources
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow28OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow29OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenOneFrameFiniteRows

/-! Return the structural socle theorem to the exact original one-frame
interfaces. Old normal-census drafts are not imported. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenStructuralFinitePackages
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoSixteenOneFrameFiniteRows

namespace Row28
open PrimitiveAffineDegreeTwoZeroSixteenPhysical.Row28 (Original)
open PrimitiveAffineDegreeTwoZeroSixteenActualSources.Row28 (index originalEquiv)

theorem originalQuotientSocle
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (N : Subgroup Original) [N.Normal] : SocleNormalGeneratorBound (Original ⧸ N) 2 := by
  let pi := (QuotientGroup.mk' N).comp originalEquiv.symm.toMonoidHom
  have hs : Function.Surjective pi :=
    (QuotientGroup.mk'_surjective N).comp originalEquiv.symm.surjective
  exact CyclicSocleQuotientTools.socleBound_equiv
    (QuotientGroup.quotientKerEquivOfSurjective pi hs)
    (PrimitiveAffineDegreeTwoZeroSixteenActualSources.Row28.quotientSocle socle hMN pi.ker)

def family (socle : PublishedPrimitiveSocleDichotomyInput)
    (hMN : McIverNeumannPermutationGeneratorBound) :
    DegreeTwoZeroSixteenInterfaces.row28.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    DegreeTwoZeroSixteenInterfaces.row28.normalRegistry
    (fun N => by letI := N.2; exact originalQuotientSocle socle hMN N.1)

def finiteData (socle : PublishedPrimitiveSocleDichotomyInput)
    (hMN : McIverNeumannPermutationGeneratorBound) :
    DegreeTwoSixteenOneFrameFiniteRowData DegreeTwoZeroSixteenInterfaces.row28 :=
  .ofCertificates (family socle hMN) PrimitiveAffineDegreeTwoZeroSixteenRow28OrbitWitness.natural

def catalogueFiniteData (socle : PublishedPrimitiveSocleDichotomyInput)
    (hMN : McIverNeumannPermutationGeneratorBound) :
    DegreeTwoSixteenOneFrameFiniteRowData
      (DegreeTwoSixteenPairFiniteCatalogue.catalogue.zero16 (27 : Fin 29)) :=
  finiteData socle hMN

end Row28

namespace Row29
open PrimitiveAffineDegreeTwoZeroSixteenPhysical.Row29 (Original)
open PrimitiveAffineDegreeTwoZeroSixteenActualSources.Row29 (index originalEquiv)

theorem originalQuotientSocle
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (N : Subgroup Original) [N.Normal] : SocleNormalGeneratorBound (Original ⧸ N) 2 := by
  let pi := (QuotientGroup.mk' N).comp originalEquiv.symm.toMonoidHom
  have hs : Function.Surjective pi :=
    (QuotientGroup.mk'_surjective N).comp originalEquiv.symm.surjective
  exact CyclicSocleQuotientTools.socleBound_equiv
    (QuotientGroup.quotientKerEquivOfSurjective pi hs)
    (PrimitiveAffineDegreeTwoZeroSixteenActualSources.Row29.quotientSocle socle hMN pi.ker)

def family (socle : PublishedPrimitiveSocleDichotomyInput)
    (hMN : McIverNeumannPermutationGeneratorBound) :
    DegreeTwoZeroSixteenInterfaces.row29.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    DegreeTwoZeroSixteenInterfaces.row29.normalRegistry
    (fun N => by letI := N.2; exact originalQuotientSocle socle hMN N.1)

def finiteData (socle : PublishedPrimitiveSocleDichotomyInput)
    (hMN : McIverNeumannPermutationGeneratorBound) :
    DegreeTwoSixteenOneFrameFiniteRowData DegreeTwoZeroSixteenInterfaces.row29 :=
  .ofCertificates (family socle hMN) PrimitiveAffineDegreeTwoZeroSixteenRow29OrbitWitness.natural

def catalogueFiniteData (socle : PublishedPrimitiveSocleDichotomyInput)
    (hMN : McIverNeumannPermutationGeneratorBound) :
    DegreeTwoSixteenOneFrameFiniteRowData
      (DegreeTwoSixteenPairFiniteCatalogue.catalogue.zero16 (28 : Fin 29)) :=
  finiteData socle hMN

end Row29
end PrimitiveAffineDegreeTwoZeroSixteenStructuralFinitePackages
end SymmetricSubgroupAsymptotics
end
