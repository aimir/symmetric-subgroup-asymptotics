import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightGeneratedRows
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow8FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow9FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow10FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow17FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow22FinitePackage

/-!
# Complete paired-eight catalogue

The five remaining literal packages fill exactly the complement of the
nineteen-row installed catalogue. The structural-to-registry adapter then
supplies the original finite-row boundary, retaining each actual quotient
and the complete tower realization. No row-specific capacity input remains
in this twenty-four-entry catalogue.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairedEightCompleteCatalogue

/-- Fill the exact complement of the checked nineteen-row partial catalogue. -/
noncomputable def remainingRows : RemainingInstalledPairedEightData where
  row j hj := by
    rw [installedPairedEightCatalogue_mem_covered_iff] at hj
    by_cases h8 : j = 7
    · subst j
      exact PrimitiveAffineDegreeTwoPairedEightRow8FinitePackage.finiteData
    by_cases h9 : j = 8
    · subst j
      exact PrimitiveAffineDegreeTwoPairedEightRow9FinitePackage.finiteData
    by_cases h10 : j = 9
    · subst j
      exact PrimitiveAffineDegreeTwoPairedEightRow10FinitePackage.finiteData
    by_cases h17 : j = 16
    · subst j
      exact PrimitiveAffineDegreeTwoPairedEightRow17FinitePackage.finiteData
    have h22 : j = 21 := by omega
    subst j
    exact PrimitiveAffineDegreeTwoPairedEightRow22FinitePackage.finiteData

/-- An all-normal structural package for every literal retained top. -/
noncomputable def completeRow (j : Fin 24) :
    DegreeTwoPairedEightStructuralFiniteRowData
      (DegreeTwoPairedEightSharedTops.interface j) :=
  installedPairedEightCatalogue.complete remainingRows j

/-- The existing ordinary finite catalogue, with every row supplied internally. -/
noncomputable def finiteCatalogue : DegreeTwoPairedEightFiniteCatalogueData :=
  DegreeTwoPairedEightFiniteCatalogueData.ofStructuralRows completeRow

/-- Compatibility with the earlier boundary that supplied the first row separately. -/
noncomputable def remainingFiniteRows : RemainingDegreeTwoPairedEightFiniteRowData :=
  finiteCatalogue.toRemaining

/-- Resolve every actual paired-eight tower using only its published character inputs. -/
noncomputable def resolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (j : Fin 24) {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization (DegreeTwoPairedEightSharedTops.interface j) p) :
    DegreeTwoPairTopResolvedRow (DegreeTwoPairedEightSharedTops.interface j)
      degreeTwoSixteenPairProfiles p :=
  remainingRows.resolvedRow hZmud lit j R

end DegreeTwoPairedEightCompleteCatalogue
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
