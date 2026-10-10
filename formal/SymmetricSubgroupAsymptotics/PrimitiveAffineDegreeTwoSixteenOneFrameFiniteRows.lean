import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenPairFiniteCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopStructuralAnchor
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopConcreteBranches

/-!
# Finite packages for the one-frame count-sixteen rows

The zero16, twoAffine16, and primitive16 catalogues have the same reusable
Schur profile.  A two-position quotient-socle family and a four-generator
bound on the natural binary permutation module give the permitted
ordinary-relative profile `(2,4)`.  The universal Schur lift then resolves
every realization of the literal top.

This file records that common two-certificate package and its one generic
converter.  Generated files for all three families need only export a value
of this package.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoSixteenOneFrameFiniteRows

/-- The smallest common finite package for a literal one-frame
count-sixteen top. -/
structure DegreeTwoSixteenOneFrameFiniteRowData
    (D : DegreeTwoPairTopFiniteInterface 16) : Type 1 where
  topSocle : D.normalRegistry.QuotientSocleGeneratorFamily 2
  natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) D.top (Fin 16)) 4

namespace DegreeTwoSixteenOneFrameFiniteRowData

variable {D : DegreeTwoPairTopFiniteInterface 16}
  (F : DegreeTwoSixteenOneFrameFiniteRowData D)

/-- Named constructor for an independently generated count-sixteen
one-frame package. -/
noncomputable def ofCertificates
    (topSocle : D.normalRegistry.QuotientSocleGeneratorFamily 2)
    (natural : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin 16)) 4) :
    DegreeTwoSixteenOneFrameFiniteRowData D where
  topSocle := topSocle
  natural := natural

/-- Install the two finite certificates in the common `(2,4)` Schur row. -/
noncomputable def schurData
    {p : PreE7PairActionClass 16}
    {R : DegreeTwoPairTopRealization D p} :
    DegreeTwoPairTopSchurData D p R :=
  DegreeTwoPairTopSchurData.ofUniform 2 4 F.topSocle F.natural

/-- Resolve every realization of this literal top with the common
count-sixteen profile menu. -/
noncomputable def liftConclusion
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopRealization D p) :
    DegreeTwoPairTopRelativeLiftConclusion D p :=
  (F.schurData (R := R)).liftConclusion hZmud lit
    degreeTwoSixteenPairProfiles
    degreeTwoSixteenPairProfiles_capacity
    (by native_decide)

/-- Catalogue-facing resolved row constructed from the finite package. -/
noncomputable def resolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopRealization D p) :
    DegreeTwoPairTopResolvedRow D degreeTwoSixteenPairProfiles p := by
  let lift := F.liftConclusion hZmud lit R
  exact .relative lift rfl (degreeTwoSixteenPairRelativeNumerics lift.lift)

end DegreeTwoSixteenOneFrameFiniteRowData

namespace Catalogue

namespace Rows := DegreeTwoSixteenPairFiniteCatalogue

/-- Complete finite packages for the 29 zero16, 15 twoAffine16, and 20
primitive16 rows. -/
structure DegreeTwoSixteenOneFrameFiniteCatalogueData : Type 1 where
  zero16 : ∀ j : Fin 29,
    DegreeTwoSixteenOneFrameFiniteRowData
      (Rows.catalogue.zero16 j)
  twoAffine16 : ∀ j : Fin 15,
    DegreeTwoSixteenOneFrameFiniteRowData
      (Rows.catalogue.twoAffine16 j)
  primitive16 : ∀ j : Fin 20,
    DegreeTwoSixteenOneFrameFiniteRowData
      (Rows.catalogue.primitive16 j)

/-- The unemitted packages after the generated third primitive row is
removed from the declaration boundary. -/
structure RemainingDegreeTwoSixteenOneFrameFiniteRowData : Type 1 where
  zero16 : ∀ j : Fin 29,
    DegreeTwoSixteenOneFrameFiniteRowData
      (Rows.catalogue.zero16 j)
  twoAffine16 : ∀ j : Fin 15,
    DegreeTwoSixteenOneFrameFiniteRowData
      (Rows.catalogue.twoAffine16 j)
  primitive16 : ∀ (j : Fin 20), j ≠ (2 : Fin 20) →
    DegreeTwoSixteenOneFrameFiniteRowData
      (Rows.catalogue.primitive16 j)

/-- Insert the generated primitive16-3 package into the complete one-frame
catalogue. -/
noncomputable def ofGeneratedPrimitiveRow3
    (row3 : DegreeTwoSixteenOneFrameFiniteRowData
      (Rows.catalogue.primitive16 (2 : Fin 20)))
    (F : RemainingDegreeTwoSixteenOneFrameFiniteRowData) :
    DegreeTwoSixteenOneFrameFiniteCatalogueData where
  zero16 := F.zero16
  twoAffine16 := F.twoAffine16
  primitive16 := fun j ↦ by
    by_cases hj : j = (2 : Fin 20)
    · subst j
      exact row3
    · exact F.primitive16 j hj

namespace DegreeTwoSixteenOneFrameFiniteCatalogueData

variable (F : DegreeTwoSixteenOneFrameFiniteCatalogueData)

/-- Dispatch one zero16 package through the common converter. -/
noncomputable def zero16ResolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (j : Fin 29)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopRealization (Rows.catalogue.zero16 j) p) :
    DegreeTwoPairTopResolvedRow (Rows.catalogue.zero16 j)
      degreeTwoSixteenPairProfiles p :=
  (F.zero16 j).resolvedRow hZmud lit R

/-- Dispatch one twoAffine16 package through the common converter. -/
noncomputable def twoAffine16ResolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (j : Fin 15)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopRealization (Rows.catalogue.twoAffine16 j) p) :
    DegreeTwoPairTopResolvedRow (Rows.catalogue.twoAffine16 j)
      degreeTwoSixteenPairProfiles p :=
  (F.twoAffine16 j).resolvedRow hZmud lit R

/-- Dispatch one primitive16 package through the common converter. -/
noncomputable def primitive16ResolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (j : Fin 20)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopRealization (Rows.catalogue.primitive16 j) p) :
    DegreeTwoPairTopResolvedRow (Rows.catalogue.primitive16 j)
      degreeTwoSixteenPairProfiles p :=
  (F.primitive16 j).resolvedRow hZmud lit R

end DegreeTwoSixteenOneFrameFiniteCatalogueData
end Catalogue
end DegreeTwoSixteenOneFrameFiniteRows
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
