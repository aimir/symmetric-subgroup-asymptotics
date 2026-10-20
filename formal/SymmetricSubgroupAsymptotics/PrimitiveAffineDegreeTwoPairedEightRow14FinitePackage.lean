import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow14CoupledHeads
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow14QuotientGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow14QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightFiniteRowData

/-!
# Complete finite package for paired-eight row 14

The coupled-head table, the generic fixed-layer descent, and the finite-table
socle theorem supply all three finite inputs of the shared paired-tower
argument. The final export retains the actual tower realization and the two
published character inputs, with no project-owned capacity premise.
-/

-- As for row one, avoid expanding dependent signatures in the optional
-- premise-suggestion index. All declarations are still kernel checked.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PrimitiveAffineDegreeTwoPairedEightRow14FinitePackage"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineDegreeTwoPairedEightRow14FinitePackage

noncomputable def coupledData :
    DegreeTwoPairTopCoupledRegistryData DegreeTwoPairedEightSharedTops.top14 4 where
  Generator := Fin 3
  State := Fin 7
  generators := PrimitiveAffineDegreeTwoPairedEightRow14NaturalModule.topAmbient
  state := PrimitiveAffineDegreeTwoPairedEightRow14NaturalModule.states
  registry := PrimitiveAffineDegreeTwoPairedEightRow14CoupledHeads.completeRegistry

/-- All finite inputs for this literal top, with every quotient witness
certified by the same finite-table theorem. -/
noncomputable def finiteData :
    DegreeTwoPairedEightStructuralFiniteRowData DegreeTwoPairedEightSharedTops.top14 :=
  DegreeTwoPairedEightStructuralFiniteRowData.ofCertificates coupledData
    PrimitiveAffineDegreeTwoPairedEightRow14QuotientGenerators.finiteGeneratorData
    PrimitiveAffineDegreeTwoPairedEightRow14QuotientSocles.topSocle

/-- Full row resolution, uniformly over every retained actual tower. -/
noncomputable def resolvedLiteralRowClosed
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization DegreeTwoPairedEightSharedTops.top14 p) :
    DegreeTwoPairTopResolvedRow DegreeTwoPairedEightSharedTops.top14
      degreeTwoSixteenPairProfiles p :=
  ((finiteData.rowData hZmud R).sixteenResolvedData lit).toResolvedRow

end PrimitiveAffineDegreeTwoPairedEightRow14FinitePackage
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
