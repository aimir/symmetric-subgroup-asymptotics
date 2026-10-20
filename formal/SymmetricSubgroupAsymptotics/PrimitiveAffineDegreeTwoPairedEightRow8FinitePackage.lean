import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightTop8
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow8CoupledHeads
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow8QuotientGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow8QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightFiniteRowData

/-! Complete finite package for paired-eight row 8, using its semantic
all-normal quotient-socle theorem and its retained literal generators. -/

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PrimitiveAffineDegreeTwoPairedEightRow8FinitePackage"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineDegreeTwoPairedEightRow8FinitePackage

noncomputable def coupledData :
    DegreeTwoPairTopCoupledRegistryData DegreeTwoPairedEightSharedTops.top8 4 where
  Generator := Fin 8
  State := Fin 6
  generators := PrimitiveAffineDegreeTwoPairedEightRow8NaturalModule.topAmbient
  state := PrimitiveAffineDegreeTwoPairedEightRow8NaturalModule.states
  registry := PrimitiveAffineDegreeTwoPairedEightRow8CoupledHeads.completeRegistry

/-- Explicit adapter to the structural constructor's all-normal signature.
The narrow interface's top is definitionally this literal generator closure. -/
theorem topSocle
    (N : {N : Subgroup DegreeTwoPairedEightSharedTops.top8.top // N.Normal}) :
    SocleNormalGeneratorBound (DegreeTwoPairedEightSharedTops.top8.top ⧸ N.1) 2 :=
  PrimitiveAffineDegreeTwoPairedEightRow8QuotientSocles.topSocle N

noncomputable def finiteData :
    DegreeTwoPairedEightStructuralFiniteRowData DegreeTwoPairedEightSharedTops.top8 :=
  DegreeTwoPairedEightStructuralFiniteRowData.ofCertificates coupledData
    PrimitiveAffineDegreeTwoPairedEightRow8QuotientGenerators.finiteGeneratorData topSocle

/-- Full row resolution, uniformly over every retained actual tower. -/
noncomputable def resolvedLiteralRowClosed
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization DegreeTwoPairedEightSharedTops.top8 p) :
    DegreeTwoPairTopResolvedRow DegreeTwoPairedEightSharedTops.top8
      degreeTwoSixteenPairProfiles p :=
  ((finiteData.rowData hZmud R).sixteenResolvedData lit).toResolvedRow

end PrimitiveAffineDegreeTwoPairedEightRow8FinitePackage
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
