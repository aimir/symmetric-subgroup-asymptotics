import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow2CoupledHeads
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow2QuotientGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow2QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightFiniteRowData

/-!
# Complete finite package for paired-eight row two

The coupled-head table, the generic fixed-layer descent, and the normal-chain
socle theorem supply all three finite inputs of the shared paired-tower
argument. The final export retains the actual tower realization and the two
published character inputs, with no project-owned capacity premise.
-/

-- As for row one, avoid expanding dependent signatures in the optional
-- premise-suggestion index. All declarations are still kernel checked.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PrimitiveAffineDegreeTwoPairedEightRow2FinitePackage"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineDegreeTwoPairedEightRow2FinitePackage

noncomputable def coupledData :
    DegreeTwoPairTopCoupledRegistryData DegreeTwoPairedEightSharedTops.top2 4 where
  Generator := Fin 4
  State := Fin 13
  generators := PrimitiveAffineDegreeTwoPairedEightRow2NaturalModule.topAmbient
  state := PrimitiveAffineDegreeTwoPairedEightRow2NaturalModule.states
  registry := PrimitiveAffineDegreeTwoPairedEightRow2CoupledHeads.completeRegistry

/-- All finite inputs for this literal top, established without a separate
normal-generating tuple for each quotient. -/
noncomputable def finiteData :
    DegreeTwoPairedEightStructuralFiniteRowData DegreeTwoPairedEightSharedTops.top2 :=
  DegreeTwoPairedEightStructuralFiniteRowData.ofCertificates coupledData
    PrimitiveAffineDegreeTwoPairedEightRow2QuotientGenerators.finiteGeneratorData
    PrimitiveAffineDegreeTwoPairedEightRow2QuotientSocles.topSocle

/-- Full row resolution, uniformly over every retained actual tower. -/
noncomputable def resolvedLiteralRowClosed
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization DegreeTwoPairedEightSharedTops.top2 p) :
    DegreeTwoPairTopResolvedRow DegreeTwoPairedEightSharedTops.top2
      degreeTwoSixteenPairProfiles p :=
  ((finiteData.rowData hZmud R).sixteenResolvedData lit).toResolvedRow

end PrimitiveAffineDegreeTwoPairedEightRow2FinitePackage
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
