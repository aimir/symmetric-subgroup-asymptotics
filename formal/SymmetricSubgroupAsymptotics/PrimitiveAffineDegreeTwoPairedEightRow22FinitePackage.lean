import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightTop22
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow22CoupledHeads
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow22QuotientGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow22QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightFiniteRowData

/-! Complete finite package for paired-eight row 22, using its semantic
all-normal quotient-socle theorem and its retained literal generators. -/

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PrimitiveAffineDegreeTwoPairedEightRow22FinitePackage"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineDegreeTwoPairedEightRow22FinitePackage

noncomputable def coupledData :
    DegreeTwoPairTopCoupledRegistryData DegreeTwoPairedEightSharedTops.top22 4 where
  Generator := Fin 3
  State := Fin 4
  generators := PrimitiveAffineDegreeTwoPairedEightRow22NaturalModule.topAmbient
  state := PrimitiveAffineDegreeTwoPairedEightRow22NaturalModule.states
  registry := PrimitiveAffineDegreeTwoPairedEightRow22CoupledHeads.completeRegistry

/-- Explicit adapter to the structural constructor's all-normal signature.
The narrow interface's top is definitionally this literal generator closure. -/
theorem topSocle
    (N : {N : Subgroup DegreeTwoPairedEightSharedTops.top22.top // N.Normal}) :
    SocleNormalGeneratorBound (DegreeTwoPairedEightSharedTops.top22.top ⧸ N.1) 2 :=
  PrimitiveAffineDegreeTwoPairedEightRow22QuotientSocles.topSocle N

noncomputable def finiteData :
    DegreeTwoPairedEightStructuralFiniteRowData DegreeTwoPairedEightSharedTops.top22 :=
  DegreeTwoPairedEightStructuralFiniteRowData.ofCertificates coupledData
    PrimitiveAffineDegreeTwoPairedEightRow22QuotientGenerators.finiteGeneratorData topSocle

/-- Full row resolution, uniformly over every retained actual tower. -/
noncomputable def resolvedLiteralRowClosed
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization DegreeTwoPairedEightSharedTops.top22 p) :
    DegreeTwoPairTopResolvedRow DegreeTwoPairedEightSharedTops.top22
      degreeTwoSixteenPairProfiles p :=
  ((finiteData.rowData hZmud R).sixteenResolvedData lit).toResolvedRow

end PrimitiveAffineDegreeTwoPairedEightRow22FinitePackage
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
