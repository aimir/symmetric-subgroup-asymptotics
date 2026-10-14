import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightCoupledCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow2FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow3FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow4FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow5FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow6FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow7FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow11FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow23FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow24FinitePackage

/-!
# Install ten complete paired-eight rows

Finite quotient-socle tuples and the normal-chain theorem feed the same
all-normal package. The first seven rows, row eleven, and the natural
alternating and symmetric tops leave fourteen entries as explicit obligations.
-/

-- Keep concrete catalogue signatures out of the optional suggestion index.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "generatedPairedEightFirstTwo"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "RemainingDegreeTwoPairedEightAfterTwoData"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "generatedPairedEightFirstThree"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "RemainingDegreeTwoPairedEightAfterThreeData"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "generatedPairedEightFirstFour"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "RemainingDegreeTwoPairedEightAfterData"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "RemainingDegreeTwoPairedEightAfterFourData"

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "generatedPairedEightFirstFive"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "RemainingDegreeTwoPairedEightAfterFiveData"

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "generatedPairedEightFirstFiveCatalogue"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "installedPairedEightCatalogue"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "RemainingInstalledPairedEightData"

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

noncomputable def generatedPairedEightFirstFive
    (j : Fin 24) (hj : j.val < 5) :
    DegreeTwoPairedEightStructuralFiniteRowData (DegreeTwoPairedEightSharedTops.interface j) := by
  by_cases hfour : j.val < 4
  · exact generatedPairedEightFirstFour j hfour
  · have hfive : j = 4 := by omega
    subst j
    exact PrimitiveAffineDegreeTwoPairedEightRow5FinitePackage.finiteData

/-- Nineteen finite packages remain after the five installed rows. -/
abbrev RemainingDegreeTwoPairedEightAfterFiveData := RemainingDegreeTwoPairedEightAfterData 5

noncomputable def RemainingDegreeTwoPairedEightAfterFiveData.resolvedRow
    (F : RemainingDegreeTwoPairedEightAfterFiveData)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (j : Fin 24) {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization (DegreeTwoPairedEightSharedTops.interface j) p) :
    DegreeTwoPairTopResolvedRow (DegreeTwoPairedEightSharedTops.interface j)
      degreeTwoSixteenPairProfiles p :=
  F.resolvedWith generatedPairedEightFirstFive hZmud lit j R

/-- The existing prefix is one input to the generic partial-catalogue dispatcher. -/
noncomputable def generatedPairedEightFirstFiveCatalogue :
    DegreeTwoPairedEightPartialCatalogueData DegreeTwoPairedEightSharedTops.interface where
  covered := Finset.univ.filter (fun j : Fin 24 ↦ j.val < 5)
  row j hj := generatedPairedEightFirstFive j (Finset.mem_filter.mp hj).2

/-- Install the remaining checked packages through the shared extension operation. -/
noncomputable def installedPairedEightCatalogue :
    DegreeTwoPairedEightPartialCatalogueData DegreeTwoPairedEightSharedTops.interface :=
  ((((generatedPairedEightFirstFiveCatalogue.add 5
    PrimitiveAffineDegreeTwoPairedEightRow6FinitePackage.finiteData).add 6
    PrimitiveAffineDegreeTwoPairedEightRow7FinitePackage.finiteData).add 10
    PrimitiveAffineDegreeTwoPairedEightRow11FinitePackage.finiteData).add 22
    PrimitiveAffineDegreeTwoPairedEightRow23FinitePackage.finiteData).add 23
    PrimitiveAffineDegreeTwoPairedEightRow24FinitePackage.finiteData

theorem installedPairedEightCatalogue_mem_covered_iff (j : Fin 24) :
    j ∈ installedPairedEightCatalogue.covered ↔ j.val < 7 ∨ j.val = 10 ∨ 22 ≤ j.val := by
  change (j ∈ insert (23 : Fin 24) (insert (22 : Fin 24)
    (insert (10 : Fin 24) (insert (6 : Fin 24) (insert (5 : Fin 24)
      (Finset.univ.filter (fun j : Fin 24 ↦ j.val < 5))))))) ↔ _
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

theorem installedPairedEightCatalogue_covered_card :
    installedPairedEightCatalogue.covered.card = 10 := by
  change (insert (23 : Fin 24) (insert (22 : Fin 24)
    (insert (10 : Fin 24) (insert (6 : Fin 24) (insert (5 : Fin 24)
      (Finset.univ.filter (fun j : Fin 24 ↦ j.val < 5))))))).card = 10
  decide +kernel

/-- The remaining boundary excludes exactly the installed ten packages. -/
abbrev RemainingInstalledPairedEightData := installedPairedEightCatalogue.Remaining

noncomputable def RemainingInstalledPairedEightData.resolvedRow
    (F : RemainingInstalledPairedEightData)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (j : Fin 24) {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization (DegreeTwoPairedEightSharedTops.interface j) p) :
    DegreeTwoPairTopResolvedRow (DegreeTwoPairedEightSharedTops.interface j)
      degreeTwoSixteenPairProfiles p :=
  installedPairedEightCatalogue.resolvedRow F hZmud lit j R

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
