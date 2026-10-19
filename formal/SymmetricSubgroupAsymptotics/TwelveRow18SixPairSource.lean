import SymmetricSubgroupAsymptotics.TwelveRow18OriginalModelMap
import SymmetricSubgroupAsymptotics.TernaryCentralComplementSocles
import SymmetricSubgroupAsymptotics.DirectBinaryFactorSixPairSource

/-! The original row18 is the actual image of (D6 × C3) × C2.
The first factor has a proved one-generator bound on every normal quotient;
the binary factor supplies the linear character on the SAME original axes. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelveRow18SixPairSource
open Non2UnipotentPrefixFiniteMenu
open TwelveRow18DihedralCentralModel
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelvePairFiniteCatalogue

 theorem factor_socle (M : Subgroup (D × C3)) [M.Normal] :
    SocleNormalGeneratorBound ((D × C3) ⧸ M) 1 :=
  quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    TernaryCentralComplementSocles.dihedral_product_normal_singletons M

/-- Exact representative-facing source with all original normal axes. -/
def source (hZmud : ZmudFaithfulCharacterTupleInput)
    (p : PreE7PairActionClass 6) (e : Row18Top ≃* preE7PairAction 6 p) :
    PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p) :=
  DirectBinaryFactorSixPairSource.source factor_socle hZmud p
    (e.toMonoidHom.comp originalMap) (e.surjective.comp originalMap_surjective)

end SymmetricSubgroupAsymptotics.TwelveRow18SixPairSource
