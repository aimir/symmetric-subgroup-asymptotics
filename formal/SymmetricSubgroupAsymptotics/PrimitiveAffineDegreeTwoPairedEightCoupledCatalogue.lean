import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightSharedTops
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1QuotientGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightFiniteRowData

/-!
# Coupled-head registries for the paired-eight catalogue

Each of the twenty-four paired-eight slots supplies one finite coupled-head
registry on its literal degree-eight top.  The registry is declared before
any tower realization is chosen.  A single structural theorem then installs
it on every realization and bounds the fixed part of raw omega by four.

The first row is already generated.  Consequently the remaining catalogue
input consists of twenty-three finite registry declarations rather than
twenty-three representation inequalities or resolved-row assumptions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer


/-- Realization-free coupled registries for all paired-eight catalogue
slots. -/
structure DegreeTwoPairedEightCoupledCatalogueData : Type 1 where
  row : ∀ j : Fin 24,
    DegreeTwoPairTopCoupledRegistryData (DegreeTwoPairedEightSharedTops.interface j) 4

/-- The still-unemitted part of the paired-eight coupled catalogue.  Every
field is a finite registry declaration on a literal top. -/
structure RemainingDegreeTwoPairedEightCoupledRegistryData : Type 1 where
  row : ∀ (j : Fin 24), j ≠ (0 : Fin 24) →
    DegreeTwoPairTopCoupledRegistryData (DegreeTwoPairedEightSharedTops.interface j) 4

/-- The already generated finite declaration for paired8-1. -/
noncomputable def generatedPairedEightRow1FiniteData :
    DegreeTwoPairedEightFiniteRowData DegreeTwoPairedEightSharedTops.top1 where
  coupled := SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads.finiteCoupledHeadData
  quotientGenerators := SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1QuotientGenerators.finiteGeneratorData
  topSocle := DegreeTwoPairedEightRow1QuotientSocles.family

/-- Finite row declarations for the twenty-three paired-eight slots after
the generated first row. -/
structure RemainingDegreeTwoPairedEightFiniteRowData : Type 1 where
  row : ∀ (j : Fin 24), j ≠ (0 : Fin 24) →
    DegreeTwoPairedEightFiniteRowData (DegreeTwoPairedEightSharedTops.interface j)

/-- Complete finite declarations for all paired-eight slots. -/
structure DegreeTwoPairedEightFiniteCatalogueData : Type 1 where
  row : ∀ j : Fin 24,
    DegreeTwoPairedEightFiniteRowData (DegreeTwoPairedEightSharedTops.interface j)

namespace DegreeTwoPairedEightFiniteCatalogueData

noncomputable def ofGeneratedRow1
    (F : RemainingDegreeTwoPairedEightFiniteRowData) :
    DegreeTwoPairedEightFiniteCatalogueData where
  row := fun j ↦ by
    by_cases hj : j = (0 : Fin 24)
    · subst j
      exact generatedPairedEightRow1FiniteData
    · exact F.row j hj

variable (F : DegreeTwoPairedEightFiniteCatalogueData)

noncomputable def coupled : DegreeTwoPairedEightCoupledCatalogueData where
  row := fun j ↦ (F.row j).coupled

/-- Dispatch the finite declarations to a full semantic row without any
slot-specific representation premise. -/
noncomputable def rowData
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (j : Fin 24) {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization (DegreeTwoPairedEightSharedTops.interface j) p) :
    DegreeTwoPairTopTowerRelativeKernelOrbitRowData
      (DegreeTwoPairedEightSharedTops.interface j) degreeTwoSixteenPairProfiles p R :=
  (F.row j).rowData hZmud R

end DegreeTwoPairedEightFiniteCatalogueData

namespace DegreeTwoPairedEightCoupledCatalogueData

/-- Combine the generated first row with finite declarations for the other
twenty-three rows. -/
noncomputable def ofGeneratedRow1
    (C : RemainingDegreeTwoPairedEightCoupledRegistryData) :
    DegreeTwoPairedEightCoupledCatalogueData where
  row := fun j ↦ by
    by_cases hj : j = (0 : Fin 24)
    · subst j
      exact SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads.finiteCoupledHeadData
    · exact C.row j hj

variable (C : DegreeTwoPairedEightCoupledCatalogueData)

/-- Install the finite registry for one catalogue slot on an arbitrary
actual two-frame realization. -/
noncomputable def towerData
    (j : Fin 24) {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization (DegreeTwoPairedEightSharedTops.interface j) p) :
    DegreeTwoPairTopTowerCoupledHeadData R 4 :=
  (C.row j).towerData R

include C in
/-- Catalogue-wide fixed-row dispatch: the same structural bridge closes
all twenty-four raw fixed-omega inequalities. -/
theorem rawKernelOmega_invariants_finrank_le_four
    (j : Fin 24) {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization (DegreeTwoPairedEightSharedTops.interface j) p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal}) :
    Module.finrank (ZMod 2)
        (binaryKernelOmegaConjugationRepresentation
          (R.rawQuotientMap N)).invariants ≤ 4 :=
  (C.row j).rawKernelOmega_invariants_finrank_le R N

end DegreeTwoPairedEightCoupledCatalogueData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
