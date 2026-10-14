import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow19CoupledHeads
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow19QuotientGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow19QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightFiniteRowData

/-!
# Complete finite package for paired-eight row 19

The coupled-head table, the generic fixed-layer descent, and the finite-table
socle theorem supply all three finite inputs of the shared paired-tower
argument. The final export retains the actual tower realization and the two
published character inputs, with no project-owned capacity premise.
-/

-- As for row one, avoid expanding dependent signatures in the optional
-- premise-suggestion index. All declarations are still kernel checked.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PrimitiveAffineDegreeTwoPairedEightRow19FinitePackage"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineDegreeTwoPairedEightRow19FinitePackage

noncomputable def coupledData :
    DegreeTwoPairTopCoupledRegistryData DegreeTwoPairedEightSharedTops.top19 4 where
  Generator := Fin 3
  State := Fin 5
  generators := PrimitiveAffineDegreeTwoPairedEightRow19NaturalModule.topAmbient
  state := PrimitiveAffineDegreeTwoPairedEightRow19NaturalModule.states
  registry := PrimitiveAffineDegreeTwoPairedEightRow19CoupledHeads.completeRegistry

/-- All finite inputs for this literal top, with every quotient witness
certified by the same finite-table theorem. -/
noncomputable def finiteData :
    DegreeTwoPairedEightStructuralFiniteRowData DegreeTwoPairedEightSharedTops.top19 :=
  DegreeTwoPairedEightStructuralFiniteRowData.ofCertificates coupledData
    PrimitiveAffineDegreeTwoPairedEightRow19QuotientGenerators.finiteGeneratorData
    PrimitiveAffineDegreeTwoPairedEightRow19QuotientSocles.topSocle

/-- Full row resolution, uniformly over every retained actual tower. -/
noncomputable def resolvedLiteralRowClosed
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization DegreeTwoPairedEightSharedTops.top19 p) :
    DegreeTwoPairTopResolvedRow DegreeTwoPairedEightSharedTops.top19
      degreeTwoSixteenPairProfiles p :=
  ((finiteData.rowData hZmud R).sixteenResolvedData lit).toResolvedRow

end PrimitiveAffineDegreeTwoPairedEightRow19FinitePackage
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
