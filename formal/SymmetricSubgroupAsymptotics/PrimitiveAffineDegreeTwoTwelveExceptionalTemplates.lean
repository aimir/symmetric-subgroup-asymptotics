import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopRelativeKernelOrbitRows

/-!
# Shared templates for the exceptional count-twelve branches

The ten relative exceptional rows and the eight ternary rows use two
different endpoints.  A core or paired-six row retains a finite two-axis
profile table together with explicit prefix/kernel-orbit inputs on its
actual quotients.  A ternary row retains the ordinary finite QCHAR data for
the compressed action.  These are raw construction inputs rather than
resolved-row premises.

One converter below constructs each complete relative row from the
profile/orbit package.  A second converter installs a QCHAR package in any
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

/-- Raw profile and orbit data shared by the binary-core and paired-six
families.  The state table is finite and declared on the literal top.  The
last field records the concrete prefix and omega-orbit construction on the
actual quotient selected by those states. -/
structure DegreeTwoTwelveExceptionalOrbitPackage
    (D : DegreeTwoPairTopFiniteInterface 12) : Type 1 where
  profileOfState : D.normalRegistry.State → D.ModuleState →
    DegreeTwoPairRelativeProfile
  profile_mem : ∀ i j,
    profileOfState i j ∈ degreeTwoTwelvePairExceptionalProfiles
  input : ∀ (p : PreE7PairActionClass 12)
    (R : DegreeTwoPairTopRealization D p)
    (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal}),
    DegreeTwoPairRelativeKernelOrbitInput
      (preE7PairAction 12 p ⧸ N.1)
      (profileOfState (R.topNormalState N) (R.moduleState N))

/-- Family name for the eight binary-core packages. -/
abbrev DegreeTwoTwelveCoreOrbitPackage :=
  DegreeTwoTwelveExceptionalOrbitPackage

/-- Family name for the two paired-six packages. -/
abbrev DegreeTwoTwelvePairedSixOrbitPackage :=
  DegreeTwoTwelveExceptionalOrbitPackage

namespace DegreeTwoTwelveExceptionalOrbitPackage

variable {D : DegreeTwoPairTopFiniteInterface 12}
  (F : DegreeTwoTwelveExceptionalOrbitPackage D)

/-- The shared finite-profile conversion for both exceptional relative
families. -/
noncomputable def rowData
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p) :
    DegreeTwoPairTopRelativeKernelOrbitRowData D
      degreeTwoTwelvePairExceptionalProfiles p R where
  stateProfile :=
    { profileOfState := F.profileOfState
      allowedProfiles := degreeTwoTwelvePairExceptionalProfiles
      allowed_capacity := degreeTwoTwelvePairExceptionalProfiles_capacity
      profile_mem := fun N ↦
        F.profile_mem (R.topNormalState N) (R.moduleState N) }
  profiles_eq := rfl
  input := F.input p R

/-- Install one core or paired-six package at a literal exceptional
catalogue row. -/
noncomputable def catalogueResolvedRow
    {row : DegreeTwoTwelvePairTopRow}
    (F : DegreeTwoTwelveExceptionalOrbitPackage row.finite)
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
  exact ((F.rowData R).twelveResolvedData lit).toResolvedRow

end DegreeTwoTwelveExceptionalOrbitPackage

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
    DegreeTwoTwelveCoreOrbitPackage
      (Catalogue.catalogue.row j).finite
  paired : ∀ (j : Fin 301),
    (Catalogue.catalogue.row j).branch = .paired →
    DegreeTwoTwelvePairedSixOrbitPackage
      (Catalogue.catalogue.row j).finite
  ternary : ∀ (j : Fin 301),
    (Catalogue.catalogue.row j).branch = .ternary →
    DegreeTwoTwelveTernaryQcharPackage
      (Catalogue.catalogue.row j).finite

namespace DegreeTwoTwelveExceptionalCatalogueData

variable (F : DegreeTwoTwelveExceptionalCatalogueData)

/-- Uniform dispatch for one binary-core row. -/
noncomputable def coreResolvedRow
    (lit : PreE7CharacterLiterature)
    (j : Fin 301)
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization
      (Catalogue.catalogue.row j).finite p)
    (hbranch : (Catalogue.catalogue.row j).branch = .core) :
    DegreeTwoPairTopResolvedRow
      (Catalogue.catalogue.row j).finite
      (Catalogue.catalogue.row j).expectedProfiles p :=
  (F.core j hbranch).catalogueResolvedRow lit (Or.inl hbranch) R

/-- Uniform dispatch for one paired-six row. -/
noncomputable def pairedResolvedRow
    (lit : PreE7CharacterLiterature)
    (j : Fin 301)
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization
      (Catalogue.catalogue.row j).finite p)
    (hbranch : (Catalogue.catalogue.row j).branch = .paired) :
    DegreeTwoPairTopResolvedRow
      (Catalogue.catalogue.row j).finite
      (Catalogue.catalogue.row j).expectedProfiles p :=
  (F.paired j hbranch).catalogueResolvedRow lit (Or.inr hbranch) R

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
