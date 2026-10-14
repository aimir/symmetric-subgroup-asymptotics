import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightCoupledCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow2FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow3FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow4FinitePackage

/-!
# Install the first four complete paired-eight rows

Finite quotient-socle tuples and the normal-chain theorem feed the same
all-normal package. The remaining boundary has twenty entries: the
first four rows are supplied here, rather than requested again as inputs.
-/

-- Keep concrete catalogue signatures out of the optional suggestion index.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "generatedPairedEightFirstTwo"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "RemainingDegreeTwoPairedEightAfterTwoData"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "generatedPairedEightFirstThree"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "RemainingDegreeTwoPairedEightAfterThreeData"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "generatedPairedEightFirstFour"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "RemainingDegreeTwoPairedEightAfterData"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "RemainingDegreeTwoPairedEightAfterFourData"

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

/-- The third row is discharged by the uniform module and two-chain proofs. -/
noncomputable def generatedPairedEightFirstThree
    (j : Fin 24) (hj : j.val < 3) :
    DegreeTwoPairedEightStructuralFiniteRowData (DegreeTwoPairedEightSharedTops.interface j) := by
  by_cases htwo : j.val < 2
  · exact generatedPairedEightFirstTwo j htwo
  · have hthree : j = 2 := by omega
    subst j
    exact PrimitiveAffineDegreeTwoPairedEightRow3FinitePackage.finiteData

/-- The twenty-one finite packages not yet installed by this dispatcher. -/
structure RemainingDegreeTwoPairedEightAfterThreeData : Type 1 where
  row : ∀ (j : Fin 24), 3 ≤ j.val →
    DegreeTwoPairedEightStructuralFiniteRowData (DegreeTwoPairedEightSharedTops.interface j)

namespace RemainingDegreeTwoPairedEightAfterThreeData

/-- Compatibility with the existing endpoint, supplying row three internally. -/
noncomputable def toAfterTwo (F : RemainingDegreeTwoPairedEightAfterThreeData) :
    RemainingDegreeTwoPairedEightAfterTwoData where
  row j _ := if hj : j.val < 3 then generatedPairedEightFirstThree j hj
    else F.row j (Nat.le_of_not_gt hj)

noncomputable def resolvedRow
    (F : RemainingDegreeTwoPairedEightAfterThreeData)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (j : Fin 24) {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization (DegreeTwoPairedEightSharedTops.interface j) p) :
    DegreeTwoPairTopResolvedRow (DegreeTwoPairedEightSharedTops.interface j)
      degreeTwoSixteenPairProfiles p :=
  F.toAfterTwo.resolvedRow hZmud lit j R

end RemainingDegreeTwoPairedEightAfterThreeData

/-- A generic remaining-row boundary avoids a new assembly proof per installed prefix. -/
structure RemainingDegreeTwoPairedEightAfterData (installed : ℕ) : Type 1 where
  row : ∀ (j : Fin 24), installed ≤ j.val →
    DegreeTwoPairedEightStructuralFiniteRowData (DegreeTwoPairedEightSharedTops.interface j)

namespace RemainingDegreeTwoPairedEightAfterData

noncomputable def completeWith {installed : ℕ}
    (F : RemainingDegreeTwoPairedEightAfterData installed)
    (installedRows : ∀ (j : Fin 24), j.val < installed →
      DegreeTwoPairedEightStructuralFiniteRowData (DegreeTwoPairedEightSharedTops.interface j))
    (j : Fin 24) :
    DegreeTwoPairedEightStructuralFiniteRowData (DegreeTwoPairedEightSharedTops.interface j) :=
  if hj : j.val < installed then installedRows j hj else F.row j (Nat.le_of_not_gt hj)

noncomputable def resolvedWith {installed : ℕ}
    (F : RemainingDegreeTwoPairedEightAfterData installed)
    (installedRows : ∀ (j : Fin 24), j.val < installed →
      DegreeTwoPairedEightStructuralFiniteRowData (DegreeTwoPairedEightSharedTops.interface j))
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (j : Fin 24) {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization (DegreeTwoPairedEightSharedTops.interface j) p) :
    DegreeTwoPairTopResolvedRow (DegreeTwoPairedEightSharedTops.interface j)
      degreeTwoSixteenPairProfiles p :=
  (((F.completeWith installedRows j).rowData hZmud R).sixteenResolvedData lit).toResolvedRow

end RemainingDegreeTwoPairedEightAfterData

noncomputable def generatedPairedEightFirstFour
    (j : Fin 24) (hj : j.val < 4) :
    DegreeTwoPairedEightStructuralFiniteRowData (DegreeTwoPairedEightSharedTops.interface j) := by
  by_cases hthree : j.val < 3
  · exact generatedPairedEightFirstThree j hthree
  · have hfour : j = 3 := by omega
    subst j
    exact PrimitiveAffineDegreeTwoPairedEightRow4FinitePackage.finiteData

/-- Twenty finite packages remain after the four installed rows. -/
abbrev RemainingDegreeTwoPairedEightAfterFourData := RemainingDegreeTwoPairedEightAfterData 4

noncomputable def RemainingDegreeTwoPairedEightAfterFourData.resolvedRow
    (F : RemainingDegreeTwoPairedEightAfterFourData)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (j : Fin 24) {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization (DegreeTwoPairedEightSharedTops.interface j) p) :
    DegreeTwoPairTopResolvedRow (DegreeTwoPairedEightSharedTops.interface j)
      degreeTwoSixteenPairProfiles p :=
  F.resolvedWith generatedPairedEightFirstFour hZmud lit j R

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
