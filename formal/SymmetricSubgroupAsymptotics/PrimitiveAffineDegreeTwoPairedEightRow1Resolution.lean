import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopRelativeKernelOrbitRows
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopTowerOmegaFiltration
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopTowerNestedQuotient
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopTowerOuterNestedQuotient
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1QuotientGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenPairFiniteCatalogue

/-!
# Relative-kernel resolution of paired-eight row 1

The first paired-eight row supplies three literal finite certificates:
a top-normal socle registry, a coupled K/W/L table, and a nested-quotient
generator table. The shared paired-tower theorem turns these into the
four-position omega-socle capacity bound for every original normal subgroup.
The row-specific statements below are specializations of that shared proof.

The orbit-character layer then constructs the relative irreducibles and
resolves the literal catalogue row. The older conditional entry points remain
available beside the unconditional capacity theorem.
-/

-- Avoid the suggestion-index exporter's expansion of dependent row signatures.
-- This affects automatic premise suggestions only; kernel checking is unchanged.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PrimitiveAffineDegreeTwoPairedEightRow1Resolution"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineDegreeTwoPairedEightRow1Resolution


local instance finiteAsModule {G V : Type} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (rho : Representation (ZMod 2) G V) : Finite rho.asModule :=
  Finite.of_equiv V rho.asModuleEquiv.symm.toEquiv

local instance finiteDimensionalSubmodule {G V : Type} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [Module (ZMod 2)[G] V]
    [IsScalarTower (ZMod 2) (ZMod 2)[G] V]
    [FiniteDimensional (ZMod 2) V]
    (X : Submodule (ZMod 2)[G] V) : FiniteDimensional (ZMod 2) X :=
  FiniteDimensional.of_injective
    (X.subtype.restrictScalars (ZMod 2)) X.subtype_injective

local instance innerOmegaFinite
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal}) :
    Finite (R.innerOmegaSubrepresentation N).toSubmodule :=
  Finite.of_surjective _ (R.rawKernelOmegaInnerImageIntertwiner_surjective N)

local instance innerOmegaFiniteDimensional
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal}) :
    FiniteDimensional (ZMod 2) (R.innerOmegaSubrepresentation N).toSubmodule :=
  Module.Finite.of_finite

/-- The checked coupled table applies to the three actual omega axes for
every original normal subgroup of every realization of this row. -/
theorem omegaHeadDemand_le_four
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal}) :
    (SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads.towerCoupledHeadData R).omegaHeadDemand N ≤ 4 :=
  (SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads.towerCoupledHeadData R).omegaHeadDemand_le N

/-- For row 1 the four stored permutations generate the literal top, so
the checked demand is the intrinsic three-layer expression with the full
commutator/coinvariant subspace in its final denominator. -/
theorem omegaHeadDemand_eq_intrinsic
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal}) :
    (SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads.towerCoupledHeadData R).omegaHeadDemand N =
      Module.finrank (ZMod 2)
          (R.innerOmegaNaturalAxis N).toRepresentation.Coinvariants +
        Module.finrank (ZMod 2)
          (R.outerOmegaPairSumAxis N).toRepresentation.Coinvariants +
        Module.finrank (ZMod 2)
          ((R.outerOmegaConstantAxis N).toSubmodule ⧸
            ((binaryCoordinateProductSpan
                (R.innerOmegaNaturalAxis N).toSubmodule
                (R.outerOmegaPairSumAxis N).toSubmodule).comap
                  (R.outerOmegaConstantAxis N).toSubmodule.subtype ⊔
              Representation.Coinvariants.ker
                (R.outerOmegaConstantAxis N).toRepresentation)) :=
  (SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads.towerCoupledHeadData R).omegaHeadDemand_eq_intrinsic
    SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.topAmbient_full N

/-- The row-1 table's third term as its concrete pointwise-fixed quotient
of the actual constant omega axis. -/
abbrev OmegaCoupledQuotientRepresentation
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal}) :=
  (SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads.towerCoupledHeadData R).omegaCoupledQuotientRepresentation
    SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.topAmbient_full N

@[simp] theorem omegaCoupledQuotientRepresentation_apply
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal})
    (g : SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.Top)
    (z : (OmegaCoupledQuotientRepresentation R N).asModule) :
    OmegaCoupledQuotientRepresentation R N g z = z :=
  (SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads.towerCoupledHeadData R).omegaCoupledQuotientRepresentation_apply
      SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.topAmbient_full N g z

theorem omegaCoupledQuotient_invariants_finrank_eq_demandThird
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal}) :
    Module.finrank (ZMod 2)
        (OmegaCoupledQuotientRepresentation R N).invariants =
      Module.finrank (ZMod 2)
        ((R.outerOmegaConstantAxis N).toSubmodule ⧸
          binaryCoupledDenominator
            (permutationFunctionRepresentation (ZMod 2) SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.Top (Fin 8))
            SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.topAmbient (R.outerOmegaConstantAxis N)
            (binaryCoordinateProductSpan
              (R.innerOmegaNaturalAxis N).toSubmodule
              (R.outerOmegaPairSumAxis N).toSubmodule)
            (R.omegaAxes_productSpan_le N)) :=
  (SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads.towerCoupledHeadData R).omegaCoupledQuotientRepresentation_invariants_finrank_eq
      SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.topAmbient_full N

/-- The generated cap-four table now bounds three literal representation
rows: the K and W invariant-form heads and the fixed residual L quotient. -/
theorem omegaRepresentationRows_le_four
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal}) :
    Module.finrank (ZMod 2)
        ((R.innerOmegaNaturalAxis N).toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod 2) SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.Top (ZMod 2))) +
      Module.finrank (ZMod 2)
        ((R.outerOmegaPairSumAxis N).toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod 2) SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.Top (ZMod 2))) +
      Module.finrank (ZMod 2)
        (OmegaCoupledQuotientRepresentation R N).invariants ≤ 4 := by
  exact ((SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads.towerCoupledHeadData R).omegaHeadDemand_eq_head_add_head_add_fixed
      SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.topAmbient_full N).symm.trans_le
    (omegaHeadDemand_le_four R N)

/-- The natural representation carried by the canonical socle of the
central omega of one actual direct quotient kernel. -/
abbrev OmegaSocleRepresentation
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal}) :=
  (finiteRepresentationSocle
    (binaryKernelOmegaConjugationRepresentation
      (R.rawQuotientMap N))).toRepresentation

/-- The canonical socle contains every fixed omega vector, so its fixed
row is exactly the fixed row of the full raw omega representation. -/
theorem omegaSocle_invariants_finrank_eq_rawOmega
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 p)
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
    (R : DegreeTwoPairTopTowerRealization SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal})
    (hraw : Module.finrank (ZMod 2)
      (binaryKernelOmegaConjugationRepresentation
        (R.rawQuotientMap N)).invariants ≤
          (SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads.towerCoupledHeadData R).omegaHeadDemand N) :
    Module.finrank (ZMod 2)
      (OmegaSocleRepresentation R N).invariants ≤
        (SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads.towerCoupledHeadData R).omegaHeadDemand N := by
  rw [omegaSocle_invariants_finrank_eq_rawOmega R N]
  exact hraw

/-- Nonfixed simple rows may likewise be computed in the full raw omega
module: every simple-source map already lands in the canonical socle. -/
theorem omegaSocle_schurSocleMultiplicity_eq_rawOmega
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 p)
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

/-- The first concrete nonfixed-row split: socle multiplicity is bounded
by the literal kernel and inner image of the omega projection. -/
theorem omegaSocle_schurSocleMultiplicity_le_projectionKernel_add_inner
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal})
    (X : Submodule (ZMod 2)[preE7PairAction 16 p ⧸ N.1]
      (OmegaSocleRepresentation R N).asModule)
    [IsSimpleModule (ZMod 2)[preE7PairAction 16 p ⧸ N.1] X] :
    schurSocleMultiplicity
        (k := ZMod 2)
        (R := (ZMod 2)[preE7PairAction 16 p ⧸ N.1])
        (A := (OmegaSocleRepresentation R N).asModule) (X := X) ≤
      schurSocleMultiplicity
          (k := ZMod 2)
          (R := (ZMod 2)[preE7PairAction 16 p ⧸ N.1])
          (A := (R.rawKernelOmegaInnerImageIntertwiner N).ker.asSubmodule)
          (X := X) +
        schurSocleMultiplicity
          (k := ZMod 2)
          (R := (ZMod 2)[preE7PairAction 16 p ⧸ N.1])
          (A := (inflatedRepresentation (R.rawQuotientMap N)
            (R.innerOmegaSubrepresentation N).toRepresentation).asModule) (X := X) := by
  exact SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1QuotientGenerators.finiteGeneratorData.omegaSocle_schurSocleMultiplicity_le_projectionKernel_add_inner R N X

/-- Over the actual first pair top, every nonfixed simple row in the retained
outer quotient costs at most two Schur dimensions.  The exact pair-sum map
splits it into two nested quotients of paired-eight states, each covered by
the uniform finite quotient theorem. -/
theorem outerNestedQuotient_nonfixed_schurSocleMultiplicity_le_two_mul
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal})
    {A : Type} [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
    (sigma : Representation (ZMod 2) R.frame.top.range A)
    (X : Submodule (ZMod 2)[R.frame.top.range] sigma.asModule)
    [Finite X] [IsSimpleModule (ZMod 2)[R.frame.top.range] X]
    (hnonfixed : ¬ representationSubmoduleFixed sigma X) :
    schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[R.frame.top.range])
        (A := (nestedQuotientRepresentation
          (R.frame.normalTopPermutationSubrepresentation N.1)
          (R.outerOmegaAxis N)
          (R.outerNormalAxis_le_outerOmegaAxis N)).asModule) (X := X) ≤
      2 * Module.finrank
        (Module.End (ZMod 2)[R.frame.top.range] X) X := by
  exact SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1QuotientGenerators.finiteGeneratorData.outerNestedQuotient_comp_nonfixed_le_two_mul
    R N (MonoidHom.id R.frame.top.range) Function.surjective_id sigma X hnonfixed

/-- The same two-layer estimate after pullback along any surjective action
map onto the first pair top.  This is the form used after inflating the
physical outer kernel back to the original action. -/
theorem outerNestedQuotient_comp_nonfixed_le_two_mul
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal})
    {H A : Type} [Group H]
    (gamma : H →* R.frame.top.range)
    (hgamma : Function.Surjective gamma)
    [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
    (sigma : Representation (ZMod 2) H A)
    (X : Submodule (ZMod 2)[H] sigma.asModule)
    [Finite X] [IsSimpleModule (ZMod 2)[H] X]
    (hnonfixed : ¬ representationSubmoduleFixed sigma X) :
    schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[H])
        (A := (inflatedRepresentation gamma (nestedQuotientRepresentation
          (R.frame.normalTopPermutationSubrepresentation N.1)
          (R.outerOmegaAxis N)
          (R.outerNormalAxis_le_outerOmegaAxis N))).asModule)
        (X := X) ≤
      2 * Module.finrank (Module.End (ZMod 2)[H] X) X := by
  exact SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1QuotientGenerators.finiteGeneratorData.outerNestedQuotient_comp_nonfixed_le_two_mul
    R N gamma hgamma sigma X hnonfixed

/-- Every nonfixed simple row in the actual inner omega image costs one
Schur dimension. Ordinary state quotients use the cyclic-dual table;
the three exceptions use a binary plane or certified fixed upper layers. -/
theorem innerOmega_nonfixed_schurSocleMultiplicity_le_end_finrank
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal})
    (X : Submodule (ZMod 2)[preE7PairAction 16 p ⧸ N.1]
      (OmegaSocleRepresentation R N).asModule)
    [IsSimpleModule (ZMod 2)[preE7PairAction 16 p ⧸ N.1] X]
    (hnonfixed : ¬ representationSubmoduleFixed
      (OmegaSocleRepresentation R N) X) :
    schurSocleMultiplicity
        (k := ZMod 2)
        (R := (ZMod 2)[preE7PairAction 16 p ⧸ N.1])
        (A := (inflatedRepresentation (R.rawQuotientMap N)
          (R.innerOmegaSubrepresentation N).toRepresentation).asModule) (X := X) ≤
      Module.finrank
        (Module.End (ZMod 2)[preE7PairAction 16 p ⧸ N.1] X) X := by
  exact SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1QuotientGenerators.finiteGeneratorData.innerOmega_nonfixed_schurSocleMultiplicity_le_end_finrank R N X hnonfixed

/-- Every nonfixed simple row in the physical outer projection kernel costs
two Schur dimensions.  The proof inflates the actual kernel and simple row
back to the original action, uses the action-level identification with
`B/A`, applies the two endpoint quotient theorem, and descends the resulting
multiplicity unchanged. -/
theorem outerOmega_nonfixed_schurSocleMultiplicity_le_two_mul_end_finrank
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal})
    (X : Submodule (ZMod 2)[preE7PairAction 16 p ⧸ N.1]
      (OmegaSocleRepresentation R N).asModule)
    [IsSimpleModule (ZMod 2)[preE7PairAction 16 p ⧸ N.1] X]
    (hnonfixed : ¬ representationSubmoduleFixed
      (OmegaSocleRepresentation R N) X) :
    schurSocleMultiplicity
        (k := ZMod 2)
        (R := (ZMod 2)[preE7PairAction 16 p ⧸ N.1])
        (A := (R.rawKernelOmegaInnerImageIntertwiner N).ker.asSubmodule)
        (X := X) ≤
      2 * Module.finrank
        (Module.End (ZMod 2)[preE7PairAction 16 p ⧸ N.1] X) X := by
  exact SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1QuotientGenerators.finiteGeneratorData.outerOmega_nonfixed_schurSocleMultiplicity_le_two_mul_end_finrank R N X hnonfixed

/-- The physical outer and inner estimates close the complete nonfixed row
of the omega socle with the required coefficient three. -/
theorem omegaSocle_nonfixed_schurSocleMultiplicity_le_three_mul_end_finrank
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal})
    (X : Submodule (ZMod 2)[preE7PairAction 16 p ⧸ N.1]
      (OmegaSocleRepresentation R N).asModule)
    [IsSimpleModule (ZMod 2)[preE7PairAction 16 p ⧸ N.1] X]
    (hnonfixed : ¬ representationSubmoduleFixed
      (OmegaSocleRepresentation R N) X) :
    schurSocleMultiplicity
        (k := ZMod 2)
        (R := (ZMod 2)[preE7PairAction 16 p ⧸ N.1])
        (A := (OmegaSocleRepresentation R N).asModule) (X := X) ≤
      3 * Module.finrank
        (Module.End (ZMod 2)[preE7PairAction 16 p ⧸ N.1] X) X := by
  exact SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1QuotientGenerators.finiteGeneratorData.omegaSocle_nonfixed_schurSocleMultiplicity_le_three_mul_end_finrank R N X hnonfixed

/-- The checked coupled head closes the fixed simple row; a three-layer
same-simple-type multiplicity estimate closes every nonfixed row.  This
is the exact algebraic composition of those two inputs for one actual
original normal subgroup. -/
theorem omegaSocle_schurCapacity_le_four_of_coupled_nonfixed
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal})
    (hfixed : Module.finrank (ZMod 2)
      (OmegaSocleRepresentation R N).invariants ≤
        (SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads.towerCoupledHeadData R).omegaHeadDemand N)
    (hnonfixed : ∀ X : Submodule
      (ZMod 2)[preE7PairAction 16 p ⧸ N.1]
        (OmegaSocleRepresentation R N).asModule,
      [IsSimpleModule (ZMod 2)[preE7PairAction 16 p ⧸ N.1] X] →
      ¬ representationSubmoduleFixed (OmegaSocleRepresentation R N) X →
      schurSocleMultiplicity
          (k := ZMod 2)
          (R := (ZMod 2)[preE7PairAction 16 p ⧸ N.1])
          (A := (OmegaSocleRepresentation R N).asModule) (X := X) ≤
        3 * Module.finrank
          (Module.End (ZMod 2)[preE7PairAction 16 p ⧸ N.1] X) X) :
    representationSchurCapacity (OmegaSocleRepresentation R N) ≤ 4 := by
  apply representationSchurCapacity_le_of_fixed_nonfixed_multiplicity
    (OmegaSocleRepresentation R N) 4
  · exact hfixed.trans (omegaHeadDemand_le_four R N)
  · intro X hX hXfixed
    have hthree := hnonfixed X hXfixed
    exact hthree.trans (by omega)

/-- The natural omega-socle capacity conclusion for every original normal
subgroup. The theorem below supplies it from the coupled registry and the
three same-top permutation-module sections. -/
abbrev OmegaSocleSchurCapacityLeFour
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 p) : Prop :=
  ∀ N, representationSchurCapacity
    (OmegaSocleRepresentation R N) ≤ 4

/-- Compatibility constructor from a raw fixed-row bound and nonfixed
representation inequalities. Both inputs are supplied by the unconditional
capacity theorem below. -/
theorem omegaSocleSchurCapacityLeFour_of_rawCoupled_nonfixed
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 p)
    (hraw : ∀ N,
      Module.finrank (ZMod 2)
          (binaryKernelOmegaConjugationRepresentation
            (R.rawQuotientMap N)).invariants ≤
        (SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads.towerCoupledHeadData R).omegaHeadDemand N)
    (hnonfixed : ∀ N
      (X : Submodule (ZMod 2)[preE7PairAction 16 p ⧸ N.1]
        (OmegaSocleRepresentation R N).asModule),
      [IsSimpleModule (ZMod 2)[preE7PairAction 16 p ⧸ N.1] X] →
      ¬ representationSubmoduleFixed (OmegaSocleRepresentation R N) X →
      schurSocleMultiplicity
          (k := ZMod 2)
          (R := (ZMod 2)[preE7PairAction 16 p ⧸ N.1])
          (A := (OmegaSocleRepresentation R N).asModule) (X := X) ≤
        3 * Module.finrank
          (Module.End (ZMod 2)[preE7PairAction 16 p ⧸ N.1] X) X) :
    OmegaSocleSchurCapacityLeFour R := by
  intro N
  apply omegaSocle_schurCapacity_le_four_of_coupled_nonfixed R N
  · exact omegaSocle_invariants_le_of_rawOmega R N (hraw N)
  · exact hnonfixed N

/-- Compatibility constructor from a raw fixed-row bound, using the proved
physical outer and inner layer estimates for the nonfixed rows. -/
theorem omegaSocleSchurCapacityLeFour_of_rawCoupled
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 p)
    (hraw : ∀ N,
      Module.finrank (ZMod 2)
          (binaryKernelOmegaConjugationRepresentation
            (R.rawQuotientMap N)).invariants ≤
        (SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads.towerCoupledHeadData R).omegaHeadDemand N) :
    OmegaSocleSchurCapacityLeFour R := by
  apply omegaSocleSchurCapacityLeFour_of_rawCoupled_nonfixed R hraw
  intro N X _hX hnonfixed
  exact omegaSocle_nonfixed_schurSocleMultiplicity_le_three_mul_end_finrank
    R N X hnonfixed

/-- The generated coupled registry and the two actual pair sections close
the fixed row, while the physical three-layer theorem closes every nonfixed
row.  Thus paired8-1 needs no residual representation premise. -/
theorem omegaSocleSchurCapacityLeFour
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 p) :
    OmegaSocleSchurCapacityLeFour R := by
  intro N
  exact SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1QuotientGenerators.finiteGeneratorData.omegaSocle_schurCapacity_le_four
    SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads.finiteCoupledHeadData R N

/-- Concrete orbit-character row for paired8-1.  The two ordinary prefix
positions come from the checked quotient-socle family; the four relative
positions are converted into literal central characters and irreducible
whole-quotient representations by the universal orbit theorem. -/
noncomputable def rowData
    (hZmud : ZmudFaithfulCharacterTupleInput)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 p)
    (socleCapacity : OmegaSocleSchurCapacityLeFour R) :
    DegreeTwoPairTopTowerRelativeKernelOrbitRowData
      SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 degreeTwoSixteenPairProfiles p R :=
  DegreeTwoPairTopTowerRelativeKernelOrbitRowData.ofOrdinaryRelativeRawSocleSchurCapacity hZmud 2 4
      (by decide +kernel)
      degreeTwoSixteenPairProfiles_capacity
      (fun N ↦
        (SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightRow1QuotientSocles.family.data (R.topNormalState N)).quotientSocleGenerator)
      socleCapacity

/-- Catalogue-facing resolution of literal paired-eight index zero. -/
noncomputable def resolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization
      (SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoSixteenPairFiniteCatalogue.catalogue.paired8 (0 : Fin 24)) p)
    (socleCapacity : OmegaSocleSchurCapacityLeFour R) :
    DegreeTwoPairTopResolvedRow
      (SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoSixteenPairFiniteCatalogue.catalogue.paired8 (0 : Fin 24))
      degreeTwoSixteenPairProfiles p :=
  ((rowData hZmud R socleCapacity).sixteenResolvedData lit).toResolvedRow

/-- The actual catalogue row, with its capacity supplied by the checked
finite coupled and quotient-generator certificates. -/
noncomputable def resolvedRowClosed
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization
      (SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoSixteenPairFiniteCatalogue.catalogue.paired8 (0 : Fin 24)) p) :
    DegreeTwoPairTopResolvedRow
      (SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoSixteenPairFiniteCatalogue.catalogue.paired8 (0 : Fin 24))
      degreeTwoSixteenPairProfiles p :=
  resolvedRow hZmud lit R (omegaSocleSchurCapacityLeFour R)

end PrimitiveAffineDegreeTwoPairedEightRow1Resolution
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
