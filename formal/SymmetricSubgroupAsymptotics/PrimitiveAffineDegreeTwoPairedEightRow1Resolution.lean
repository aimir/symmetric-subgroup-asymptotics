import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopRelativeKernelOrbitRows
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopTowerOmegaFiltration
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenPairFiniteCatalogue

/-!
# Relative-kernel resolution of paired-eight row 1

The first paired-eight row already has two independent literal finite
certificates.  Its top-normal registry supplies two ordinary prefix
characters, and its coupled K/W/L table proves the exact four-position
head inequality for every original normal subgroup.  This file attaches
those certificates to the actual direct two-frame quotient and isolates
the remaining representation-theoretic conclusion: four generators of
the dual of that quotient kernel's canonical omega socle.

Once that conclusion is supplied, the orbit-character layer constructs
the relative irreducibles and resolves the literal catalogue row.  No
binary-kernel row, relative-character tuple, or resolved-row premise is
accepted here.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineDegreeTwoPairedEightRow1Resolution

namespace Shared := DegreeTwoPairedEightSharedTops
namespace Catalogue := DegreeTwoSixteenPairFiniteCatalogue
namespace Socles := DegreeTwoPairedEightRow1QuotientSocles
namespace Coupled :=
  SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads

/-- The checked coupled table applies to the three actual omega axes for
every original normal subgroup of every realization of this row. -/
theorem omegaHeadDemand_le_four
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization Shared.top1 p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal}) :
    (Coupled.towerCoupledHeadData R).omegaHeadDemand N ≤ 4 :=
  (Coupled.towerCoupledHeadData R).omegaHeadDemand_le N

/-- The natural representation carried by the canonical socle of the
central omega of one actual direct quotient kernel. -/
abbrev OmegaSocleRepresentation
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization Shared.top1 p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal}) :=
  (finiteRepresentationSocle
    (binaryKernelOmegaConjugationRepresentation
      (R.rawQuotientMap N))).toRepresentation

/-- The canonical socle contains every fixed omega vector, so its fixed
row is exactly the fixed row of the full raw omega representation. -/
theorem omegaSocle_invariants_finrank_eq_rawOmega
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization Shared.top1 p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal}) :
    Module.finrank (ZMod 2)
        (OmegaSocleRepresentation R N).invariants =
      Module.finrank (ZMod 2)
        (binaryKernelOmegaConjugationRepresentation
          (R.rawQuotientMap N)).invariants := by
  exact finiteRepresentationSocle_invariants_finrank_eq
    (binaryKernelOmegaConjugationRepresentation (R.rawQuotientMap N))

theorem omegaSocle_invariants_le_of_rawOmega
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization Shared.top1 p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal})
    (hraw : Module.finrank (ZMod 2)
      (binaryKernelOmegaConjugationRepresentation
        (R.rawQuotientMap N)).invariants ≤
          (Coupled.towerCoupledHeadData R).omegaHeadDemand N) :
    Module.finrank (ZMod 2)
      (OmegaSocleRepresentation R N).invariants ≤
        (Coupled.towerCoupledHeadData R).omegaHeadDemand N := by
  rw [R.omegaSocle_invariants_finrank_eq_rawOmega N]
  exact hraw

/-- Nonfixed simple rows may likewise be computed in the full raw omega
module: every simple-source map already lands in the canonical socle. -/
theorem omegaSocle_schurSocleMultiplicity_eq_rawOmega
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization Shared.top1 p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal})
    (X : Submodule (ZMod 2)[preE7PairAction 16 p ⧸ N.1]
      (OmegaSocleRepresentation R N).asModule)
    [IsSimpleModule (ZMod 2)[preE7PairAction 16 p ⧸ N.1] X] :
    schurSocleMultiplicity
        (k := ZMod 2)
        (R := (ZMod 2)[preE7PairAction 16 p ⧸ N.1])
        (A := (OmegaSocleRepresentation R N).asModule) (X := X) =
      schurSocleMultiplicity
        (k := ZMod 2)
        (R := (ZMod 2)[preE7PairAction 16 p ⧸ N.1])
        (A := (binaryKernelOmegaConjugationRepresentation
          (R.rawQuotientMap N)).asModule) (X := X) :=
  finiteRepresentationSocle_schurSocleMultiplicity_eq
    (binaryKernelOmegaConjugationRepresentation (R.rawQuotientMap N))

/-- The checked coupled head closes the fixed simple row; a three-layer
same-simple-type multiplicity estimate closes every nonfixed row.  This
is the exact algebraic composition of those two inputs for one actual
original normal subgroup. -/
theorem omegaSocle_schurCapacity_le_four_of_coupled_nonfixed
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization Shared.top1 p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal})
    (hfixed : Module.finrank (ZMod 2)
      (OmegaSocleRepresentation R N).invariants ≤
        (Coupled.towerCoupledHeadData R).omegaHeadDemand N)
    (hnonfixed : ∀ X : Submodule
      (ZMod 2)[preE7PairAction 16 p ⨸ N.1]
        (OmegaSocleRepresentation R N).asModule,
      [IsSimpleModule (ZMod 2)[preE7PairAction 16 p ⨸ N.1] X] →
      ¬ representationSubmoduleFixed (OmegaSocleRepresentation R N) X →
      schurSocleMultiplicity
          (k := ZMod 2)
          (R := (ZMod 2)[preE7PairAction 16 p ⨸ N.1])
          (A := (OmegaSocleRepresentation R N).asModule) (X := X) ≤
        3 * Module.finrank
          (Module.End (ZMod 2)[preE7PairAction 16 p ⨸ N.1] X) X) :
    representationSchurCapacity (OmegaSocleRepresentation R N) ≤ 4 := by
  apply representationSchurCapacity_le_of_fixed_nonfixed_multiplicity
    (OmegaSocleRepresentation R N) 4
  · exact hfixed.trans (omegaHeadDemand_le_four R N)
  · intro X hX hXfixed
    have hthree := hnonfixed X hXfixed
    exact hthree.trans (by omega)

/-- Actual natural omega-socle capacity conclusion to be derived from the
checked coupled head inequality and the three same-top permutation-module
sections.  The type is tied to the direct quotient kernel for each original
normal subgroup; biduality and orbit characters are now automatic. -/
abbrev OmegaSocleSchurCapacityLeFour
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization Shared.top1 p) : Prop :=
  ∀ N, representationSchurCapacity
    (OmegaSocleRepresentation R N) ≤ 4

/-- Concrete orbit-character row for paired8-1.  The two ordinary prefix
positions come from the checked quotient-socle family; the four relative
positions are converted into literal central characters and irreducible
whole-quotient representations by the universal orbit theorem. -/
noncomputable def rowData
    (hZmud : ZmudFaithfulCharacterTupleInput)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization Shared.top1 p)
    (socleCapacity : OmegaSocleSchurCapacityLeFour R) :
    DegreeTwoPairTopTowerRelativeKernelOrbitRowData
      Shared.top1 degreeTwoSixteenPairProfiles p R :=
  DegreeTwoPairTopTowerRelativeKernelOrbitRowData.
    ofOrdinaryRelativeRawSocleSchurCapacity hZmud 2 4
      (by native_decide)
      degreeTwoSixteenPairProfiles_capacity
      (fun N ↦
        (Socles.family.data (R.topNormalState N)).quotientSocleGenerator)
      socleCapacity

/-- Catalogue-facing resolution of literal paired-eight index zero. -/
noncomputable def resolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization
      (Catalogue.catalogue.paired8 (0 : Fin 24)) p)
    (socleCapacity : OmegaSocleSchurCapacityLeFour R) :
    DegreeTwoPairTopResolvedRow
      (Catalogue.catalogue.paired8 (0 : Fin 24))
      degreeTwoSixteenPairProfiles p :=
  ((rowData hZmud R socleCapacity).sixteenResolvedData lit).toResolvedRow

end PrimitiveAffineDegreeTwoPairedEightRow1Resolution
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
