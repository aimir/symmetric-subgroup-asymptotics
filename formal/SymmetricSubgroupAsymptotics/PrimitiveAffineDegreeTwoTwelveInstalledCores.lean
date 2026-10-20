import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow10ExceptionalAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow32ExceptionalAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSixSymmetricThreeCores
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogue

/-!
# Install all eight original-quotient core certificates

The exact catalogue branch locator dispatches to the seven S₃ cores and
the C₃ core. Every certificate retains the original quotient. Only the two
factor-nine paired rows remain as inputs to the exceptional catalogue.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveInstalledCores

open DegreeTwoTwelvePairFiniteCatalogue
open DegreeTwoTwelveExceptionalOriginalQuotients

theorem core_locator (j : Fin 301) (h : branch j = .core) :
    j = 9 ∨ j = 31 ∨ j = 47 ∨ j = 135 ∨ j = 136 ∨
      j = 137 ∨ j = 138 ∨ j = 139 := by
  decide +kernel +revert

theorem paired_locator (j : Fin 301) (h : branch j = .paired) :
    j = 194 ∨ j = 235 := by
  decide +kernel +revert

def row10Certificate : RowCertificate row10Interface := by
  refine RowCertificate.ofBinaryTopSplit .binaryFour .ordinaryThree ?_ ?_
  · intro _hZmud p R N hbinary
    exact (Classical.choice
      (PrimitiveAffineDegreeTwoTwelveRow10NormalizerPrefix.binary_top_quotient_orbitInput
        R N hbinary)).anchor
  · intro hZmud p R N hnonbinary
    have hQ : ¬ IsPGroup 2 (preE7PairAction 12 p ⧸ N.1) := by
      intro hQ
      exact hnonbinary
        (hQ.of_surjective (R.quotientMap N) (R.quotientMap_surjective N))
    exact PrimitiveAffineDegreeTwoTwelveRow10OriginalGeometry.nonbinary_quotient_anchor
      R hZmud N hQ

def coreCertificate (j : Fin 301) (h : (catalogue.row j).branch = .core) :
    RowCertificate (catalogue.row j).finite := by
  apply Classical.choice
  rcases core_locator j h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨row10Certificate⟩
  · exact ⟨PrimitiveAffineDegreeTwoTwelveRow32ExceptionalAssembly.certificate⟩
  · exact ⟨DegreeTwoTwelveSixSymmetricThreeCores.Row48.certificate⟩
  · exact ⟨DegreeTwoTwelveSixSymmetricThreeCores.Row136.certificate⟩
  · exact ⟨DegreeTwoTwelveSixSymmetricThreeCores.Row137.certificate⟩
  · exact ⟨DegreeTwoTwelveSixSymmetricThreeCores.Row138.certificate⟩
  · exact ⟨DegreeTwoTwelveSixSymmetricThreeCores.Row139.certificate⟩
  · exact ⟨DegreeTwoTwelveSixSymmetricThreeCores.Row140.certificate⟩

/-- The two remaining exceptional certificates, still on their literal
original normal quotients. No completed core is requested again. -/
structure RemainingPairedData : Type 1 where
  row195 : RowCertificate row195Interface
  row236 : RowCertificate row236Interface

def RemainingPairedData.pairedCertificate (D : RemainingPairedData)
    (j : Fin 301) (h : (catalogue.row j).branch = .paired) :
    RowCertificate (catalogue.row j).finite := by
  apply Classical.choice
  rcases paired_locator j h with rfl | rfl
  · exact ⟨D.row195⟩
  · exact ⟨D.row236⟩

def RemainingPairedData.catalogueData (D : RemainingPairedData) :
    CatalogueData catalogue where
  core := coreCertificate
  paired := D.pairedCertificate

end DegreeTwoTwelveInstalledCores
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
