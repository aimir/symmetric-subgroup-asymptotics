import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightAffineLiteralTops
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow20CoupledHeads
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow20QuotientGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow20AffineSocleClosure
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightFiniteRowData

/-! Complete finite package for paired-eight row 20, using its semantic
all-normal quotient-socle theorem and its retained literal generators. -/

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PrimitiveAffineDegreeTwoPairedEightRow20FinitePackage"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineDegreeTwoPairedEightRow20FinitePackage

noncomputable def coupledData :
    DegreeTwoPairTopCoupledRegistryData DegreeTwoPairedEightSharedTops.top20 4 where
  Generator := Fin 3
  State := Fin 5
  generators := PrimitiveAffineDegreeTwoPairedEightRow20NaturalModule.topAmbient
  state := PrimitiveAffineDegreeTwoPairedEightRow20NaturalModule.states
  registry := PrimitiveAffineDegreeTwoPairedEightRow20CoupledHeads.completeRegistry

/-- Explicit adapter to the structural constructor's all-normal signature.
The narrow interface's top is definitionally this literal generator closure. -/
theorem topSocle
    (N : {N : Subgroup DegreeTwoPairedEightSharedTops.top20.top // N.Normal}) :
    SocleNormalGeneratorBound (DegreeTwoPairedEightSharedTops.top20.top ⧸ N.1) 2 :=
  PrimitiveAffineDegreeTwoPairedEightAffineTops.row20TopSocle N

noncomputable def finiteData :
    DegreeTwoPairedEightStructuralFiniteRowData DegreeTwoPairedEightSharedTops.top20 :=
  DegreeTwoPairedEightStructuralFiniteRowData.ofCertificates coupledData
    PrimitiveAffineDegreeTwoPairedEightRow20QuotientGenerators.finiteGeneratorData topSocle

/-- Full row resolution, uniformly over every retained actual tower. -/
noncomputable def resolvedLiteralRowClosed
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization DegreeTwoPairedEightSharedTops.top20 p) :
    DegreeTwoPairTopResolvedRow DegreeTwoPairedEightSharedTops.top20
      degreeTwoSixteenPairProfiles p :=
  ((finiteData.rowData hZmud R).sixteenResolvedData lit).toResolvedRow

end PrimitiveAffineDegreeTwoPairedEightRow20FinitePackage
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
