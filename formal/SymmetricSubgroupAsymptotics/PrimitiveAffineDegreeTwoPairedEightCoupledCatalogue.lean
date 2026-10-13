import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1QuotientGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopRelativeKernelOrbitRows

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

/-- The complete finite declaration consumed by one paired-eight row. -/
structure DegreeTwoPairedEightFiniteRowData
    (D : DegreeTwoPairTopFiniteInterface 8) : Type 1 where
  coupled : DegreeTwoPairTopCoupledRegistryData D 4
  quotientGenerators : DegreeTwoPairTopNestedQuotientGeneratorData D
  topSocle : D.normalRegistry.QuotientSocleGeneratorFamily 2

namespace DegreeTwoPairedEightFiniteRowData

variable {D : DegreeTwoPairTopFiniteInterface 8}
  (F : DegreeTwoPairedEightFiniteRowData D)

/-- Constructor used by one-row generated package files.  Keeping this
boundary named makes the emitted assembly file independently checkable. -/
noncomputable def ofCertificates
    (coupled : DegreeTwoPairTopCoupledRegistryData D 4)
    (quotientGenerators : DegreeTwoPairTopNestedQuotientGeneratorData D)
    (topSocle : D.normalRegistry.QuotientSocleGeneratorFamily 2) :
    DegreeTwoPairedEightFiniteRowData D where
  coupled := coupled
  quotientGenerators := quotientGenerators
  topSocle := topSocle

/-- Finite top, quotient-generator, and coupled-head declarations construct
the entire paired-eight orbit row for every tower realization. -/
noncomputable def rowData
    (hZmud : ZmudFaithfulCharacterTupleInput)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization D p) :
    DegreeTwoPairTopTowerRelativeKernelOrbitRowData
      D degreeTwoSixteenPairProfiles p R :=
  DegreeTwoPairTopTowerRelativeKernelOrbitRowData.ofOrdinaryRelativeRawSocleSchurCapacity hZmud 2 4
      (by decide +kernel)
      degreeTwoSixteenPairProfiles_capacity
      (fun N ↦
        (F.topSocle.data (R.topNormalState N)).quotientSocleGenerator)
      (fun N ↦
        F.quotientGenerators.omegaSocle_schurCapacity_le_four
          F.coupled R N)

end DegreeTwoPairedEightFiniteRowData

/-- Variant of the finite paired-eight package for named large tops whose
normal lattice is known structurally.  Its module and coupled fields are
still independently generated from the retained literal tuple, while the
socle input ranges directly over all normal subgroups. -/
structure DegreeTwoPairedEightStructuralFiniteRowData
    (D : DegreeTwoPairTopFiniteInterface 8) : Type 1 where
  coupled : DegreeTwoPairTopCoupledRegistryData D 4
  quotientGenerators : DegreeTwoPairTopNestedQuotientGeneratorData D
  topSocle : ∀ N : {N : Subgroup D.top // N.Normal},
    SocleNormalGeneratorBound (D.top ⧸ N.1) 2

namespace DegreeTwoPairedEightStructuralFiniteRowData

variable {D : DegreeTwoPairTopFiniteInterface 8}
  (F : DegreeTwoPairedEightStructuralFiniteRowData D)

/-- Named assembly boundary for one structural paired-eight package. -/
noncomputable def ofCertificates
    (coupled : DegreeTwoPairTopCoupledRegistryData D 4)
    (quotientGenerators : DegreeTwoPairTopNestedQuotientGeneratorData D)
    (topSocle : ∀ N : {N : Subgroup D.top // N.Normal},
      SocleNormalGeneratorBound (D.top ⧸ N.1) 2) :
    DegreeTwoPairedEightStructuralFiniteRowData D where
  coupled := coupled
  quotientGenerators := quotientGenerators
  topSocle := topSocle

/-- The structural all-normal socle theorem feeds the same universal
paired-tower converter as a generated normal-state family. -/
noncomputable def rowData
    (hZmud : ZmudFaithfulCharacterTupleInput)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization D p) :
    DegreeTwoPairTopTowerRelativeKernelOrbitRowData
      D degreeTwoSixteenPairProfiles p R :=
  DegreeTwoPairTopTowerRelativeKernelOrbitRowData.ofOrdinaryRelativeRawSocleSchurCapacity hZmud 2 4
      (by decide +kernel)
      degreeTwoSixteenPairProfiles_capacity
      (fun N ↦ F.topSocle
        ⟨D.normalRegistry.state (R.topNormalState N),
          D.normalRegistry.state_normal (R.topNormalState N)⟩)
      (fun N ↦
        F.quotientGenerators.omegaSocle_schurCapacity_le_four
          F.coupled R N)

end DegreeTwoPairedEightStructuralFiniteRowData

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
