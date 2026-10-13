import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow2FinitePackage

/-!
# Install the first two complete paired-eight rows

Finite quotient-socle tuples and the normal-chain theorem feed the same
all-normal package. The remaining boundary has twenty-two entries: the
first two rows are supplied here, rather than requested again as inputs.
-/

-- Keep concrete catalogue signatures out of the optional suggestion index.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "generatedPairedEightFirstTwo"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "RemainingDegreeTwoPairedEightAfterTwoData"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- A finite tuple registry supplies the all-normal version of a package. -/
noncomputable def DegreeTwoPairedEightFiniteRowData.toStructural
    {D : DegreeTwoPairTopFiniteInterface 8} (F : DegreeTwoPairedEightFiniteRowData D) :
    DegreeTwoPairedEightStructuralFiniteRowData D where
  coupled := F.coupled
  quotientGenerators := F.quotientGenerators
  topSocle := F.topSocle.dispatch

/-- Both installed entries, without any row-specific capacity hypothesis. -/
noncomputable def generatedPairedEightFirstTwo
    (j : Fin 24) (hj : j.val < 2) :
    DegreeTwoPairedEightStructuralFiniteRowData (DegreeTwoPairedEightSharedTops.interface j) := by
  by_cases hzero : j = 0
  · subst j
    exact generatedPairedEightRow1FiniteData.toStructural
  · have hone : j = 1 := by omega
    subst j
    exact PrimitiveAffineDegreeTwoPairedEightRow2FinitePackage.finiteData

/-- The finite packages still required after installing rows one and two. -/
structure RemainingDegreeTwoPairedEightAfterTwoData : Type 1 where
  row : ∀ (j : Fin 24), 2 ≤ j.val →
    DegreeTwoPairedEightStructuralFiniteRowData (DegreeTwoPairedEightSharedTops.interface j)

namespace RemainingDegreeTwoPairedEightAfterTwoData

/-- Uniform dispatch with the two checked rows supplied internally. -/
noncomputable def completeRow
    (F : RemainingDegreeTwoPairedEightAfterTwoData) (j : Fin 24) :
    DegreeTwoPairedEightStructuralFiniteRowData (DegreeTwoPairedEightSharedTops.interface j) :=
  if hj : j.val < 2 then generatedPairedEightFirstTwo j hj
  else F.row j (Nat.le_of_not_gt hj)

/-- The complete finite dispatcher feeds the existing resolved-row endpoint. -/
noncomputable def resolvedRow
    (F : RemainingDegreeTwoPairedEightAfterTwoData)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (j : Fin 24) {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization (DegreeTwoPairedEightSharedTops.interface j) p) :
    DegreeTwoPairTopResolvedRow (DegreeTwoPairedEightSharedTops.interface j)
      degreeTwoSixteenPairProfiles p :=
  (((F.completeRow j).rowData hZmud R).sixteenResolvedData lit).toResolvedRow

end RemainingDegreeTwoPairedEightAfterTwoData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
