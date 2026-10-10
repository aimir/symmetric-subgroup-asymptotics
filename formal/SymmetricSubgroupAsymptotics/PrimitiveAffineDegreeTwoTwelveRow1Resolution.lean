import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow1CayleySocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow1NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveJointFiniteRows

/-!
# Complete semantic resolution of count-twelve row 1

This file combines the checked quotient-socle family and the checked natural
binary permutation-module generator bound for `twelve-1`.  The resulting
Schur lift resolves every original normal subgroup carried by any realization
of the first literal count-twelve top.  Its only mathematical inputs are the
published Žmud and pre-E7 character statements used by the common lift.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineDegreeTwoTwelveRow1Resolution

namespace Catalogue := DegreeTwoTwelvePairFiniteCatalogue
namespace Socles :=
  SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow1CayleySocles
namespace Natural :=
  SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow1NaturalModule
namespace JointFinite := DegreeTwoTwelveJointFiniteRows

/-- The two generated row-1 certificates in the common finite package used
by every joint count-twelve row. -/
noncomputable def finiteData :
    JointFinite.DegreeTwoTwelveJointFiniteRowData
      Catalogue.row1Interface 1 1 where
  topSocle := Socles.family
  natural := by
    change UniformSubrepresentationGeneratorBound Natural.representation 1
    exact Natural.uniform

/-- The literal row-1 finite certificates in the reusable Schur-lift form. -/
noncomputable def schurData
    {p : PreE7PairActionClass 12}
    {R : DegreeTwoPairTopRealization Catalogue.row1Interface p} :
    DegreeTwoPairTopSchurData Catalogue.row1Interface p R :=
  finiteData.schurData

/-- All-original-normal lift for the first joint count-twelve row. -/
noncomputable def liftConclusion
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization Catalogue.row1Interface p) :
    DegreeTwoPairTopRelativeLiftConclusion Catalogue.row1Interface p :=
  (schurData (R := R)).liftConclusion hZmud lit
    (degreeTwoTwelvePairJointProfiles 1 1)
    (degreeTwoTwelvePairJointProfiles_capacity 1 1 (by native_decide))
    (by native_decide)

/-- Catalogue-facing resolved row.  This is a concrete endpoint rather than
an interface or a parameterized representative premise. -/
noncomputable def resolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization
      (Catalogue.catalogue.row (0 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow
      (Catalogue.catalogue.row (0 : Fin 301)).finite
      (Catalogue.catalogue.row (0 : Fin 301)).expectedProfiles p := by
  let lift := liftConclusion hZmud lit R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

end PrimitiveAffineDegreeTwoTwelveRow1Resolution
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
