import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopStructuralAnchor

/-!
# Shared templates for the exceptional count-twelve branches

The ten relative exceptional rows and the eight ternary rows use two
different endpoints.  A core or paired-six row retains one-position
quotient-socle generators and a three-generator natural-module bound.  A
ternary row retains the ordinary finite QCHAR data for the compressed
action.  These are raw construction inputs rather than resolved-row
premises.

One converter below constructs each complete relative row from its two
literal-top certificates.  A second converter installs a QCHAR package in any
ternary catalogue slot.  The literal catalogue structure then collects the
eight core packages, two paired-six packages, and eight ternary packages
without duplicating either semantic conversion.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveExceptionalTemplates

/-! ## Core and paired-six relative rows -/

/-- The two realization-free finite certificates shared by the binary-core
and paired-six families. -/
structure DegreeTwoTwelveExceptionalFiniteRowData
    (D : DegreeTwoPairTopFiniteInterface 12) : Type 1 where
  topSocle : D.normalRegistry.QuotientSocleGeneratorFamily 1
  natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) D.top (Fin 12)) 3

/-- Family name for the eight binary-core packages. -/
abbrev DegreeTwoTwelveCoreFiniteRowPackage :=
  DegreeTwoTwelveExceptionalFiniteRowData

/-- Family name for the two paired-six packages. -/
abbrev DegreeTwoTwelvePairedSixFiniteRowPackage :=
  DegreeTwoTwelveExceptionalFiniteRowData

namespace DegreeTwoTwelveExceptionalFiniteRowData

variable {D : DegreeTwoPairTopFiniteInterface 12}
  (F : DegreeTwoTwelveExceptionalFiniteRowData D)

/-- Install the two finite certificates in the common `(1,3)` Schur row. -/
noncomputable def schurData
    {p : PreE7PairActionClass 12}
    {R : DegreeTwoPairTopRealization D p} :
    DegreeTwoPairTopSchurData D p R :=
  DegreeTwoPairTopSchurData.ofUniform 1 3 F.topSocle F.natural

/-- Resolve every realization of an exceptional relative row from the
finite `(1,3)` package. -/
noncomputable def liftConclusion
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p) :
    DegreeTwoPairTopRelativeLiftConclusion D p :=
  (F.schurData (R := R)).liftConclusion hZmud lit
    degreeTwoTwelvePairExceptionalProfiles
    degreeTwoTwelvePairExceptionalProfiles_capacity
    (by native_decide)

/-- Install one core or paired-six package at a literal exceptional
catalogue row. -/
noncomputable def catalogueResolvedRow
    {row : DegreeTwoTwelvePairTopRow}
    (F : DegreeTwoTwelveExceptionalFiniteRowData row.finite)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (hbranch : row.branch = .core ∨ row.branch = .paired)
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization row.finite p) :
    DegreeTwoPairTopResolvedRow row.finite row.expectedProfiles p := by
  have hprofiles : row.expectedProfiles =
      degreeTwoTwelvePairExceptionalProfiles := by
    rcases hbranch with hcore | hpaired
    · rw [row.expectedProfiles_eq, hcore]
    · rw [row.expectedProfiles_eq, hpaired]
  rw [hprofiles]
  let lift := F.liftConclusion hZmud lit R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

end DegreeTwoTwelveExceptionalFiniteRowData

/-! ## Four-ternary-orbit comparator rows -/

/-- The raw finite QCHAR payload for one four-ternary-orbit top, uniformly
transported to every realization of that literal top. -/
structure DegreeTwoTwelveTernaryQcharPackage
    (D : DegreeTwoPairTopFiniteInterface 12) : Type 1 where
  qchar : ∀ (p : PreE7PairActionClass 12),
    DegreeTwoPairTopRealization D p →
      PreE7FiniteQcharMenuData 24
        (preE7SmallPairNonPairAction 12 (by norm_num) p)
  comparator_degree : ∀ (p : PreE7PairActionClass 12)
    (R : DegreeTwoPairTopRealization D p),
    (qchar p R).axes.degree = 8

namespace DegreeTwoTwelveTernaryQcharPackage

variable {D : DegreeTwoPairTopFiniteInterface 12}
  (F : DegreeTwoTwelveTernaryQcharPackage D)

/-- Convert the raw QCHAR fields to the common comparator package. -/
noncomputable def comparatorData
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p) :
    DegreeTwoTwelveTernaryComparatorData p where
  qchar := F.qchar p R
  comparator_degree := F.comparator_degree p R

/-- Install a QCHAR package in any literal ternary row. -/
noncomputable def catalogueResolvedRow
    {row : DegreeTwoTwelvePairTopRow}
    (F : DegreeTwoTwelveTernaryQcharPackage row.finite)
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization row.finite p) :
    DegreeTwoPairTopResolvedRow row.finite row.expectedProfiles p :=
  (F.comparatorData R).resolvedRow

end DegreeTwoTwelveTernaryQcharPackage

/-! ## Literal catalogue dispatch -/

namespace Catalogue := DegreeTwoTwelvePairFiniteCatalogue

/-- All eighteen exceptional count-twelve packages, separated by their
three actual catalogue branches. -/
structure DegreeTwoTwelveExceptionalCatalogueData : Type 1 where
  core : ∀ (j : Fin 301),
    (Catalogue.catalogue.row j).branch = .core →
    DegreeTwoTwelveCoreFiniteRowPackage
      (Catalogue.catalogue.row j).finite
  paired : ∀ (j : Fin 301),
    (Catalogue.catalogue.row j).branch = .paired →
    DegreeTwoTwelvePairedSixFiniteRowPackage
      (Catalogue.catalogue.row j).finite
  ternary : ∀ (j : Fin 301),
    (Catalogue.catalogue.row j).branch = .ternary →
    DegreeTwoTwelveTernaryQcharPackage
      (Catalogue.catalogue.row j).finite

namespace DegreeTwoTwelveExceptionalCatalogueData

variable (F : DegreeTwoTwelveExceptionalCatalogueData)

/-- Uniform dispatch for one binary-core row. -/
noncomputable def coreResolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (j : Fin 301)
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization
      (Catalogue.catalogue.row j).finite p)
    (hbranch : (Catalogue.catalogue.row j).branch = .core) :
    DegreeTwoPairTopResolvedRow
      (Catalogue.catalogue.row j).finite
      (Catalogue.catalogue.row j).expectedProfiles p :=
  (F.core j hbranch).catalogueResolvedRow hZmud lit (Or.inl hbranch) R

/-- Uniform dispatch for one paired-six row. -/
noncomputable def pairedResolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (j : Fin 301)
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization
      (Catalogue.catalogue.row j).finite p)
    (hbranch : (Catalogue.catalogue.row j).branch = .paired) :
    DegreeTwoPairTopResolvedRow
      (Catalogue.catalogue.row j).finite
      (Catalogue.catalogue.row j).expectedProfiles p :=
  (F.paired j hbranch).catalogueResolvedRow hZmud lit (Or.inr hbranch) R

/-- Uniform dispatch for one four-ternary-orbit row. -/
noncomputable def ternaryResolvedRow
    (j : Fin 301)
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization
      (Catalogue.catalogue.row j).finite p)
    (hbranch : (Catalogue.catalogue.row j).branch = .ternary) :
    DegreeTwoPairTopResolvedRow
      (Catalogue.catalogue.row j).finite
      (Catalogue.catalogue.row j).expectedProfiles p :=
  (F.ternary j hbranch).catalogueResolvedRow R

end DegreeTwoTwelveExceptionalCatalogueData
end DegreeTwoTwelveExceptionalTemplates
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
