import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightTop10
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow10CoupledHeads
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow10QuotientGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow10QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightFiniteRowData

/-! Complete finite package for paired-eight row 10, using its semantic
all-normal quotient-socle theorem and its retained literal generators. -/

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PrimitiveAffineDegreeTwoPairedEightRow10FinitePackage"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineDegreeTwoPairedEightRow10FinitePackage

noncomputable def coupledData :
    DegreeTwoPairTopCoupledRegistryData DegreeTwoPairedEightSharedTops.top10 4 where
  Generator := Fin 9
  State := Fin 6
  generators := PrimitiveAffineDegreeTwoPairedEightRow10NaturalModule.topAmbient
  state := PrimitiveAffineDegreeTwoPairedEightRow10NaturalModule.states
  registry := PrimitiveAffineDegreeTwoPairedEightRow10CoupledHeads.completeRegistry

/-- Explicit adapter to the structural constructor's all-normal signature.
The narrow interface's top is definitionally this literal generator closure. -/
theorem topSocle
    (N : {N : Subgroup DegreeTwoPairedEightSharedTops.top10.top // N.Normal}) :
    SocleNormalGeneratorBound (DegreeTwoPairedEightSharedTops.top10.top ⧸ N.1) 2 :=
  PrimitiveAffineDegreeTwoPairedEightRow10QuotientSocles.topSocle N

noncomputable def finiteData :
    DegreeTwoPairedEightStructuralFiniteRowData DegreeTwoPairedEightSharedTops.top10 :=
  DegreeTwoPairedEightStructuralFiniteRowData.ofCertificates coupledData
    PrimitiveAffineDegreeTwoPairedEightRow10QuotientGenerators.finiteGeneratorData topSocle

/-- Full row resolution, uniformly over every retained actual tower. -/
noncomputable def resolvedLiteralRowClosed
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization DegreeTwoPairedEightSharedTops.top10 p) :
    DegreeTwoPairTopResolvedRow DegreeTwoPairedEightSharedTops.top10
      degreeTwoSixteenPairProfiles p :=
  ((finiteData.rowData hZmud R).sixteenResolvedData lit).toResolvedRow

end PrimitiveAffineDegreeTwoPairedEightRow10FinitePackage
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
