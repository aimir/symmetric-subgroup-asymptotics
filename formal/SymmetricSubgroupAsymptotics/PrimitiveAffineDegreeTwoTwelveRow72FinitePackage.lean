import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow72Projection
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow131QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow72PolynomialFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveJointFiniteRows

/-! Row 72 inherits all original quotient-socle bounds through its explicit
surjective map from row 131; its natural bound is the checked polynomial witness. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveRow72FinitePackage

open DegreeTwoTwelvePairFiniteCatalogue
open DegreeTwoTwelveJointFiniteRows

theorem socle_of_surjective {Q : Type} [Group Q]
    (pi : Row72Top →* Q) (hpi : Function.Surjective pi) :
    SocleNormalGeneratorBound Q 1 :=
  PrimitiveAffineDegreeTwoTwelveRow131AffineModel.socle_of_surjective
    (pi.comp PrimitiveAffineDegreeTwoTwelveRow72Projection.originalTopMap)
    (hpi.comp PrimitiveAffineDegreeTwoTwelveRow72Projection.originalTopMap_surjective)

theorem quotientSocle (N : Subgroup Row72Top) [N.Normal] :
    SocleNormalGeneratorBound (Row72Top ⧸ N) 1 :=
  socle_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

def topSocle : row72Interface.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocle N.1)

def finiteData : DegreeTwoTwelveJointFiniteRowData row72Interface 1 1 where
  topSocle := topSocle
  natural := DegreeTwoTwelveRow72PolynomialFamily.row72Natural

def resolvedRow (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (71 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (71 : Fin 301)).finite
      (catalogue.row (71 : Fin 301)).expectedProfiles p := by
  let lift := finiteData.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

end DegreeTwoTwelveRow72FinitePackage
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
