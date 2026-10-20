import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightAffineLiteralTops
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow18CoupledHeads
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow18QuotientGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightAffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightFiniteRowData

/-! Complete finite package for paired-eight row 18, using its semantic
all-normal quotient-socle theorem and its retained literal generators. -/

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PrimitiveAffineDegreeTwoPairedEightRow18FinitePackage"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineDegreeTwoPairedEightRow18FinitePackage

noncomputable def coupledData :
    DegreeTwoPairTopCoupledRegistryData DegreeTwoPairedEightSharedTops.top18 4 where
  Generator := Fin 2
  State := Fin 5
  generators := PrimitiveAffineDegreeTwoPairedEightRow18NaturalModule.topAmbient
  state := PrimitiveAffineDegreeTwoPairedEightRow18NaturalModule.states
  registry := PrimitiveAffineDegreeTwoPairedEightRow18CoupledHeads.completeRegistry

/-- Explicit adapter to the structural constructor's all-normal signature.
The narrow interface's top is definitionally this literal generator closure. -/
theorem topSocle
    (N : {N : Subgroup DegreeTwoPairedEightSharedTops.top18.top // N.Normal}) :
    SocleNormalGeneratorBound (DegreeTwoPairedEightSharedTops.top18.top ⧸ N.1) 2 :=
  PrimitiveAffineDegreeTwoPairedEightAffineTops.row18TopSocle N

noncomputable def finiteData :
    DegreeTwoPairedEightStructuralFiniteRowData DegreeTwoPairedEightSharedTops.top18 :=
  DegreeTwoPairedEightStructuralFiniteRowData.ofCertificates coupledData
    PrimitiveAffineDegreeTwoPairedEightRow18QuotientGenerators.finiteGeneratorData topSocle

/-- Full row resolution, uniformly over every retained actual tower. -/
noncomputable def resolvedLiteralRowClosed
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization DegreeTwoPairedEightSharedTops.top18 p) :
    DegreeTwoPairTopResolvedRow DegreeTwoPairedEightSharedTops.top18
      degreeTwoSixteenPairProfiles p :=
  ((finiteData.rowData hZmud R).sixteenResolvedData lit).toResolvedRow

end PrimitiveAffineDegreeTwoPairedEightRow18FinitePackage
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
