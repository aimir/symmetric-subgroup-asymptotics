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

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
