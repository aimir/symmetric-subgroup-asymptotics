import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightCoupledCatalogue

/-!
# Structural paired-eight packages in the finite registry interface

A structural finite row already supplies the same coupled-head and nested
quotient-generator declarations as an ordinary finite row. Its all-normal
quotient-socle bound supplies the remaining registry-indexed field through
the generic reverse socle constructor. The literal top, normal registry,
and bounds are retained throughout.

The catalogue adapters consume the structural rows themselves; they add no
new certificate requirement. Restricting the resulting complete catalogue
to the rows after the existing first-row pilot supplies the paired-eight
field of the original concrete semantic-data interface.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

namespace DegreeTwoPairedEightStructuralFiniteRowData

/-- Reuse the finite declarations and construct the socle family on the
row's original normal registry from its structural quotient bounds. -/
noncomputable def toFinite
    {D : DegreeTwoPairTopFiniteInterface 8}
    (F : DegreeTwoPairedEightStructuralFiniteRowData D) :
    DegreeTwoPairedEightFiniteRowData D where
  coupled := F.coupled
  quotientGenerators := F.quotientGenerators
  topSocle :=
    FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
      D.normalRegistry F.topSocle

end DegreeTwoPairedEightStructuralFiniteRowData

namespace DegreeTwoPairedEightFiniteCatalogueData

/-- A complete structural family gives the existing ordinary finite
catalogue on exactly the same twenty-four literal interfaces. -/
noncomputable def ofStructuralRows
    (F : ∀ j : Fin 24,
      DegreeTwoPairedEightStructuralFiniteRowData
        (DegreeTwoPairedEightSharedTops.interface j)) :
    DegreeTwoPairedEightFiniteCatalogueData where
  row j := (F j).toFinite

/-- Restrict a complete ordinary finite catalogue to the original boundary
whose first-row pilot is supplied separately. -/
noncomputable def toRemaining
    (F : DegreeTwoPairedEightFiniteCatalogueData) :
    RemainingDegreeTwoPairedEightFiniteRowData where
  row j _ := F.row j

end DegreeTwoPairedEightFiniteCatalogueData

namespace RemainingDegreeTwoPairedEightFiniteRowData

/-- Install a complete structural family in the existing remaining-row
field, without changing the first-row pilot or any other semantic field. -/
noncomputable def ofStructuralRows
    (F : ∀ j : Fin 24,
      DegreeTwoPairedEightStructuralFiniteRowData
        (DegreeTwoPairedEightSharedTops.interface j)) :
    RemainingDegreeTwoPairedEightFiniteRowData :=
  (DegreeTwoPairedEightFiniteCatalogueData.ofStructuralRows F).toRemaining

end RemainingDegreeTwoPairedEightFiniteRowData

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
