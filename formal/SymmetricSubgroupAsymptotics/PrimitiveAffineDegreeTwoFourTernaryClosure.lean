import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourTernaryCatalogueMap
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourTernaryActiveBridge

/-!
# Closure of the four-ternary degree-two compression

This file sits after both the counting-facing catalogue map and the
structural socle argument.  It turns the exact degree-twenty action and the
retained whole-socle theorem into the certificate consumed by the eight
catalogue rows.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

namespace DegreeTwoFourTernaryTopStructure

variable {D : DegreeTwoPairTopFiniteInterface 12}
  (S : DegreeTwoFourTernaryTopStructure D)

/-- Assemble the exact-kernel certificate from the retained whole-socle
statement. -/
noncomputable def compressionCertificate_of_retainedSocle
    (hsocle : S.RetainedSocleTheorem)
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p) :
    DegreeTwoFourTernaryCompressionCertificate p where
  E := S.averagingSubgroup R
  compressedAction := S.compressedAction R
  compressedAction_ker := S.compressedAction_ker R
  quotientSocleGenerators := fun N hN => hsocle p R N hN

/-- The exact compression certificate, now unconditional from the active
and fixed socle bridges. -/
noncomputable def compressionCertificate
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p) :
    DegreeTwoFourTernaryCompressionCertificate p :=
  S.compressionCertificate_of_retainedSocle S.retainedSocleTheorem R

/-- The retained whole-socle theorem supplies the kernel-facing uniform
compression theorem. -/
theorem certificateTheorem_of_retainedSocle
    (hsocle : S.RetainedSocleTheorem) :
    S.CertificateTheorem := by
  intro p R
  exact ⟨S.compressionCertificate_of_retainedSocle hsocle R⟩

/-- The two action-type bounds therefore suffice for the kernel-facing
uniform compression theorem. -/
theorem certificateTheorem_of_parts
    (H : S.RetainedSoclePartsBounds) :
    S.CertificateTheorem :=
  S.certificateTheorem_of_retainedSocle
    (S.retainedSocleTheorem_of_parts H)

/-- The fixed action-type bound is intrinsic to the four-ternary structure,
so the final assembly boundary exposes only the active bound. -/
theorem certificateTheorem_of_active
    (hactive : ∀ (p : PreE7PairActionClass 12)
      (R : DegreeTwoPairTopRealization D p)
      (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal}),
      ¬ S.averagingSubgroup R ≤ N.1 →
        MarkedC4.normalGen
          (nontrivialActionSoclePart (preE7PairAction 12 p ⨸ N.1)
            (S.retainedTernaryImage R N)) ≤ 2) :
    S.CertificateTheorem :=
  S.certificateTheorem_of_parts
    { active := hactive
      fixed := S.retainedSoclePartsBounds_fixed }

/-- Unconditional kernel-facing compression theorem. -/
theorem certificateTheorem : S.CertificateTheorem := by
  intro p R
  exact ⟨S.compressionCertificate R⟩

/-- The quotient-facing form used by the counting source. -/
theorem compressionTheorem_of_retainedSocle
    (hsocle : S.RetainedSocleTheorem) :
    S.CompressionTheorem :=
  S.compressionTheorem_of_certificate
    (S.certificateTheorem_of_retainedSocle hsocle)

/-- Unconditional quotient-facing compression theorem. -/
theorem compressionTheorem : S.CompressionTheorem :=
  S.compressionTheorem_of_certificate S.certificateTheorem

end DegreeTwoFourTernaryTopStructure

open DegreeTwoTwelvePairFiniteCatalogue

/-- Assemble all eight compression packages once the active bound has been
proved uniformly for their checked structural witnesses. -/
noncomputable def DegreeTwoFourTernaryCatalogueWitnesses.packagesOfActive
    (W : DegreeTwoFourTernaryCatalogueWitnesses)
    (hactive : ∀ (r : Fin 8) (p : PreE7PairActionClass 12)
      (R : DegreeTwoPairTopRealization
        (degreeTwoFourTernaryInterface r) p)
      (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal}),
      ¬ (W.witness r).structure.averagingSubgroup R ≤ N.1 →
        MarkedC4.normalGen
          (nontrivialActionSoclePart (preE7PairAction 12 p ⨸ N.1)
            ((W.witness r).structure.retainedTernaryImage R N)) ≤ 2) :
    ∀ r : Fin 8,
      DegreeTwoTwelveFourTernaryCompressionPackage
        (degreeTwoFourTernaryInterface r) :=
  W.packages (fun r ↦
    (W.witness r).structure.certificateTheorem_of_active
      (hactive r))

/-- All eight compression packages from the checked literal witnesses and
the unconditional active/fixed structural theorem. -/
noncomputable def DegreeTwoFourTernaryCatalogueWitnesses.compressionPackages
    (W : DegreeTwoFourTernaryCatalogueWitnesses) :
    ∀ r : Fin 8,
      DegreeTwoTwelveFourTernaryCompressionPackage
        (degreeTwoFourTernaryInterface r) :=
  W.packages (fun r ↦ (W.witness r).structure.certificateTheorem)

/-- Dispatch the eight packages along the exact ternary-row locator in the
literal 301-row catalogue. -/
noncomputable def degreeTwoFourTernaryCatalogueCompression
    (P : ∀ r : Fin 8,
      DegreeTwoTwelveFourTernaryCompressionPackage
        (degreeTwoFourTernaryInterface r))
    (j : Fin 301) (p : PreE7PairActionClass 12)
    (R : DegreeTwoPairTopRealization (catalogue.row j).finite p)
    (h : (catalogue.row j).branch = .ternary) :
    DegreeTwoFourTernaryCompressionData p := by
  change branch j = .ternary at h
  obtain ⟨r, rfl⟩ := degreeTwoFourTernaryCatalogueIndex_complete j h
  let R' : DegreeTwoPairTopRealization
      (degreeTwoFourTernaryInterface r) p := by
    rw [degreeTwoFourTernaryInterface_eq_catalogue]
    exact R
  exact (P r).compression p R'

/-- Replace the old detached ternary comparator on the literal count-twelve
catalogue by the eight exact degree-twenty compression packages. -/
noncomputable def degreeTwoTwelveCatalogueResolution_of_relative_and_fourTernary
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (relative : ∀ (j : Fin 301) (p : PreE7PairActionClass 12),
      DegreeTwoPairTopRealization (catalogue.row j).finite p →
      (catalogue.row j).branch ≠ .ternary →
      DegreeTwoPairTopRelativeResolvedData (catalogue.row j).finite
        (catalogue.row j).expectedProfiles p)
    (P : ∀ r : Fin 8,
      DegreeTwoTwelveFourTernaryCompressionPackage
        (degreeTwoFourTernaryInterface r)) :
    DegreeTwoTwelvePairTopCatalogueResolution catalogue :=
  degreeTwoTwelveResolution_of_relative_and_fourTernary
    hZmud lit catalogue relative
      (degreeTwoFourTernaryCatalogueCompression P)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
