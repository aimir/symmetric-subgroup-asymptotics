import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow3CayleySocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow3NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenPairFiniteCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopStructuralAnchor

/-!
# Complete semantic resolution of primitive count-sixteen row 3

The selected literal top has a checked two-position quotient-socle family.
Its natural binary permutation module in fact needs only one cyclic
generator per invariant state; the common padding theorem promotes this to
the four-position relative profile used by the count-sixteen catalogue.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineDegreeTwoPrimitiveSixteenRow3Resolution

namespace Rows := DegreeTwoPrimitiveSixteenInterfaces
namespace Catalogue := DegreeTwoSixteenPairFiniteCatalogue
namespace Socles :=
  SymmetricSubgroupAsymptotics.
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow3CayleySocles
namespace Natural :=
  SymmetricSubgroupAsymptotics.
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow3NaturalModule

/-- The checked finite certificates, padded to the common `(2,4)` profile
used by literal degree-sixteen pair tops. -/
noncomputable def schurData
    {p : PreE7PairActionClass 16}
    {R : DegreeTwoPairTopRealization Rows.row3 p} :
    DegreeTwoPairTopSchurData Rows.row3 p R :=
  DegreeTwoPairTopSchurData.ofUniform 2 4 Socles.family (by
    change UniformSubrepresentationGeneratorBound Natural.representation 4
    exact Natural.uniform.mono (by omega))

/-- All-original-normal lift for primitive degree-sixteen row 3. -/
noncomputable def liftConclusion
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopRealization Rows.row3 p) :
    DegreeTwoPairTopRelativeLiftConclusion Rows.row3 p :=
  (schurData (R := R)).liftConclusion hZmud lit
    degreeTwoSixteenPairProfiles
    degreeTwoSixteenPairProfiles_capacity
    (by native_decide)

/-- Catalogue-facing resolved row for index `2` of the primitive family. -/
noncomputable def resolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopRealization
      (Catalogue.catalogue.primitive16 (2 : Fin 20)) p) :
    DegreeTwoPairTopResolvedRow
      (Catalogue.catalogue.primitive16 (2 : Fin 20))
      degreeTwoSixteenPairProfiles p := by
  let lift := liftConclusion hZmud lit R
  exact .relative lift rfl (degreeTwoSixteenPairRelativeNumerics lift.lift)

end PrimitiveAffineDegreeTwoPrimitiveSixteenRow3Resolution
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
