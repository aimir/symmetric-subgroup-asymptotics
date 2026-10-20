import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopRelativeKernelOrbitRows
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopQuotientGeneratorData

/-!
# Catalogue-independent assembly of paired-eight finite rows

A complete finite row supplies the coupled-head, nested-quotient and socle
certificates on one literal top. These constructors do not import other
catalogue entries, so adding a new top preserves earlier checked tables.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

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

/-- A partial catalogue records exactly which literal entries have checked
finite packages. This allows independent entries to be installed in any order. -/
structure DegreeTwoPairedEightPartialCatalogueData {n : ℕ}
    (D : Fin n → DegreeTwoPairTopFiniteInterface 8) : Type 1 where
  covered : Finset (Fin n)
  row : ∀ j, j ∈ covered → DegreeTwoPairedEightStructuralFiniteRowData (D j)

namespace DegreeTwoPairedEightPartialCatalogueData

variable {n : ℕ} {D : Fin n → DegreeTwoPairTopFiniteInterface 8}

/-- Install one complete literal package without changing any uncovered obligation. -/
noncomputable def add (F : DegreeTwoPairedEightPartialCatalogueData D)
    (j₀ : Fin n) (r : DegreeTwoPairedEightStructuralFiniteRowData (D j₀)) :
    DegreeTwoPairedEightPartialCatalogueData D where
  covered := insert j₀ F.covered
  row j hj := by
    by_cases h : j = j₀
    · subst j
      exact r
    · exact F.row j ((Finset.mem_insert.mp hj).resolve_left h)

/-- Every entry outside the installed set remains an explicit obligation. -/
structure Remaining (F : DegreeTwoPairedEightPartialCatalogueData D) : Type 1 where
  row : ∀ j, j ∉ F.covered → DegreeTwoPairedEightStructuralFiniteRowData (D j)

noncomputable def complete (F : DegreeTwoPairedEightPartialCatalogueData D)
    (R : F.Remaining) (j : Fin n) : DegreeTwoPairedEightStructuralFiniteRowData (D j) :=
  if hj : j ∈ F.covered then F.row j hj else R.row j hj

/-- Assemble every actual tower from the disjoint installed/remaining cover. -/
noncomputable def resolvedRow (F : DegreeTwoPairedEightPartialCatalogueData D)
    (rest : F.Remaining)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (j : Fin n) {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization (D j) p) :
    DegreeTwoPairTopResolvedRow (D j) degreeTwoSixteenPairProfiles p :=
  (((F.complete rest j).rowData hZmud R).sixteenResolvedData lit).toResolvedRow

end DegreeTwoPairedEightPartialCatalogueData

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
