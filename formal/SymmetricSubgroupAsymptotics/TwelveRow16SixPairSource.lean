import SymmetricSubgroupAsymptotics.TwelveRow16OriginalModelMap
import SymmetricSubgroupAsymptotics.SixPairSymmetricThreeProductSource
import SymmetricSubgroupAsymptotics.SharpThreePointTopEpiEnvelope

/-! Original row16 now consumes the checked S3-product normal-comparator
algebra on the actual width12 representative. All original normal axes are
retained; no historical capacity or normal census is consumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelveRow16SixPairSource
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelvePairFiniteCatalogue

def rowEquiv : Row16Top ≃* DegreeSixS3Product.G :=
  TwelveRow16SymmetricProductModel.originalEquiv.symm.trans
    (MulEquiv.prodCongr SharpThreePointTopEpiEnvelope.dihedralEquiv
      SharpThreePointTopEpiEnvelope.dihedralEquiv)

def source (p : PreE7PairActionClass 6) (e : Row16Top ≃* preE7PairAction 6 p) :
    PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p) :=
  SixPairSymmetricThreeProductSource.source p (e.symm.trans rowEquiv)

end SymmetricSubgroupAsymptotics.TwelveRow16SixPairSource
