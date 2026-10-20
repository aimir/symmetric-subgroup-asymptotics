import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopStructuralAnchor
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopConcreteBranches

/-!
# Finite packages for the joint count-twelve rows

Every joint row in the literal count-twelve catalogue has a singleton
ordinary-relative profile.  Its complete semantic resolution therefore
depends on only two finite certificates on the literal top: quotient-socle
generators with the stored ordinary capacity `kappa`, and a uniform generator
bound for the natural binary permutation module with the stored
`sectionCap`.

This file packages those two certificates before any realization is chosen.
One generic Schur-lift construction then resolves the package for every
realization.  Generated row files can consequently export one value of
`DegreeTwoTwelveJointFiniteRowData`, rather than a realization-indexed row
theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

namespace DegreeTwoTwelveJointFiniteRows

/-- The two realization-free finite certificates retained for a generic
joint count-twelve row. -/
structure DegreeTwoTwelveJointFiniteRowData
    (D : DegreeTwoPairTopFiniteInterface 12)
    (kappa sectionCap : ℕ) : Type 1 where
  topSocle : D.normalRegistry.QuotientSocleGeneratorFamily kappa
  natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) D.top (Fin 12)) sectionCap

/-- The package specialized to the stored capacities of one catalogue row. -/
abbrev DegreeTwoTwelveJointFiniteRowPackage
    (row : DegreeTwoTwelvePairTopRow) :=
  DegreeTwoTwelveJointFiniteRowData
    row.finite row.kappa row.sectionCap

namespace DegreeTwoTwelveJointFiniteRowData

variable {D : DegreeTwoPairTopFiniteInterface 12}
  {kappa sectionCap : ℕ}
  (F : DegreeTwoTwelveJointFiniteRowData D kappa sectionCap)

/-- Named constructor for an independently generated joint-row package. -/
noncomputable def ofCertificates
    (topSocle : D.normalRegistry.QuotientSocleGeneratorFamily kappa)
    (natural : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin 12))
      sectionCap) :
    DegreeTwoTwelveJointFiniteRowData D kappa sectionCap where
  topSocle := topSocle
  natural := natural

/-- Install the two finite certificates in the universal Schur construction.
The result is independent of every choice made by the realization. -/
noncomputable def schurData
    {p : PreE7PairActionClass 12}
    {R : DegreeTwoPairTopRealization D p} :
    DegreeTwoPairTopSchurData D p R :=
  DegreeTwoPairTopSchurData.ofUniform
    kappa sectionCap F.topSocle F.natural

/-- A finite joint-row package supplies the universal relative lift for every
realization of its literal top. -/
noncomputable def liftConclusion
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (hparameters : (kappa, sectionCap) ∈
      degreeTwoTwelvePairJointParameters)
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p) :
    DegreeTwoPairTopRelativeLiftConclusion D p :=
  (F.schurData (R := R)).liftConclusion hZmud lit
    (degreeTwoTwelvePairJointProfiles kappa sectionCap)
    (degreeTwoTwelvePairJointProfiles_capacity
      kappa sectionCap hparameters)
    (by
      simp only [DegreeTwoPairTopSchurData.profile,
        DegreeTwoTwelveJointFiniteRowData.schurData,
        DegreeTwoPairTopSchurData.ofUniform,
        degreeTwoPairOrdinaryRelativeProfile,
        degreeTwoPairRelativeProfile,
        degreeTwoTwelvePairJointProfiles, Finset.mem_singleton])

/-- The catalogue-facing resolved data produced by the generic joint-row
construction. -/
noncomputable def resolvedData
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (hparameters : (kappa, sectionCap) ∈
      degreeTwoTwelvePairJointParameters)
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p) :
    DegreeTwoPairTopRelativeResolvedData D
      (degreeTwoTwelvePairJointProfiles kappa sectionCap) p := by
  let lift := F.liftConclusion hZmud lit hparameters R
  exact
    { lift := lift
      profiles_eq := rfl
      numerics := degreeTwoTwelvePairRelativeNumerics lift.lift }

/-- Convert one finite package at a literal joint row into the exact resolved
row expected by the catalogue. -/
noncomputable def catalogueResolvedRow
    {row : DegreeTwoTwelvePairTopRow}
    (F : DegreeTwoTwelveJointFiniteRowPackage row)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (hbranch : row.branch = .joint)
    (hparameters : (row.kappa, row.sectionCap) ∈
      degreeTwoTwelvePairJointParameters)
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization row.finite p) :
    DegreeTwoPairTopResolvedRow row.finite row.expectedProfiles p := by
  have hprofiles : row.expectedProfiles =
      degreeTwoTwelvePairJointProfiles row.kappa row.sectionCap := by
    rw [row.expectedProfiles_eq, hbranch]
  rw [hprofiles]
  exact (F.resolvedData hZmud lit hparameters R).toResolvedRow

end DegreeTwoTwelveJointFiniteRowData

/-- Realization-free packages for all joint rows of a count-twelve
catalogue.  Non-joint rows carry no declaration in this structure. -/
structure DegreeTwoTwelveJointFiniteCatalogueData
    (T : DegreeTwoTwelvePairTopFiniteCatalogue) : Type 1 where
  row : ∀ (j : Fin 301), (T.row j).branch = .joint →
    DegreeTwoTwelveJointFiniteRowPackage (T.row j)

namespace DegreeTwoTwelveJointFiniteCatalogueData

variable {T : DegreeTwoTwelvePairTopFiniteCatalogue}
  (F : DegreeTwoTwelveJointFiniteCatalogueData T)

/-- Dispatch the same finite-to-Schur conversion across every joint row in
the catalogue. -/
noncomputable def resolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (parameters : ∀ j, (T.row j).branch = .joint →
      ((T.row j).kappa, (T.row j).sectionCap) ∈
        degreeTwoTwelvePairJointParameters)
    (j : Fin 301)
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (T.row j).finite p)
    (hbranch : (T.row j).branch = .joint) :
    DegreeTwoPairTopResolvedRow (T.row j).finite
      (T.row j).expectedProfiles p :=
  (F.row j hbranch).catalogueResolvedRow hZmud lit hbranch
    (parameters j hbranch) R

end DegreeTwoTwelveJointFiniteCatalogueData

namespace LiteralCatalogue

/-- The still-unemitted joint rows of the literal count-twelve catalogue.
The first row is excluded because its two certificates are already checked. -/
structure RemainingDegreeTwoTwelveJointFiniteRowData : Type 1 where
  row : ∀ (j : Fin 301), j ≠ (0 : Fin 301) →
    (DegreeTwoTwelvePairFiniteCatalogue.catalogue.row j).branch = .joint →
    DegreeTwoTwelveJointFiniteRowPackage (DegreeTwoTwelvePairFiniteCatalogue.catalogue.row j)

/-- Combine the generated first package with finite declarations for every
remaining joint row. -/
noncomputable def ofGeneratedRow1
    (row1 : DegreeTwoTwelveJointFiniteRowPackage
      (DegreeTwoTwelvePairFiniteCatalogue.catalogue.row (0 : Fin 301)))
    (F : RemainingDegreeTwoTwelveJointFiniteRowData) :
    DegreeTwoTwelveJointFiniteCatalogueData DegreeTwoTwelvePairFiniteCatalogue.catalogue where
  row := fun j hbranch ↦ by
    by_cases hj : j = (0 : Fin 301)
    · subst j
      exact row1
    · exact F.row j hj hbranch

end LiteralCatalogue
end DegreeTwoTwelveJointFiniteRows
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
