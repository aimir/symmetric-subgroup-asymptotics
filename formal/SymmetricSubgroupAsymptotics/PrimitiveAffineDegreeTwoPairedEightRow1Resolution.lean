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
namespace Natural := PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule
namespace QuotientGenerators :=
  PrimitiveAffineDegreeTwoPairedEightRow1QuotientGenerators
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

/-- For row 1 the four stored permutations generate the literal top, so
the checked demand is the intrinsic three-layer expression with the full
commutator/coinvariant subspace in its final denominator. -/
theorem omegaHeadDemand_eq_intrinsic
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization Shared.top1 p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal}) :
    (Coupled.towerCoupledHeadData R).omegaHeadDemand N =
      Module.finrank (ZMod 2)
          (R.innerOmegaNaturalAxis N).toRepresentation.Coinvariants +
        Module.finrank (ZMod 2)
          (R.outerOmegaPairSumAxis N).toRepresentation.Coinvariants +
        Module.finrank (ZMod 2)
          ((R.outerOmegaConstantAxis N).toSubmodule ⫽
            ((binaryCoordinateProductSpan
                (R.innerOmegaNaturalAxis N).toSubmodule
                (R.outerOmegaPairSumAxis N).toSubmodule).comap
                  (R.outerOmegaConstantAxis N).toSubmodule.subtype ⊔
              Representation.Coinvariants.ker
                (R.outerOmegaConstantAxis N).toRepresentation)) :=
  (Coupled.towerCoupledHeadData R).omegaHeadDemand_eq_intrinsic
    Natural.topAmbient_full N

/-- The row-1 table's third term as its concrete pointwise-fixed quotient
of the actual constant omega axis. -/
abbrev OmegaCoupledQuotientRepresentation
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization Shared.top1 p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal}) :=
  (Coupled.towerCoupledHeadData R).omegaCoupledQuotientRepresentation
    Natural.topAmbient_full N

@[simp] theorem omegaCoupledQuotientRepresentation_apply
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization Shared.top1 p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal})
    (g : Natural.Top)
    (z : (OmegaCoupledQuotientRepresentation R N).asModule) :
    OmegaCoupledQuotientRepresentation R N g z = z :=
  (Coupled.towerCoupledHeadData R).
    omegaCoupledQuotientRepresentation_apply
      Natural.topAmbient_full N g z

theorem omegaCoupledQuotient_invariants_finrank_eq_demandThird
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization Shared.top1 p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal}) :
    Module.finrank (ZMod 2)
        (OmegaCoupledQuotientRepresentation R N).invariants =
      Module.finrank (ZMod 2)
        ((R.outerOmegaConstantAxis N).toSubmodule ⫽
          binaryCoupledDenominator
            (permutationFunctionRepresentation (ZMod 2) Natural.Top (Fin 8))
            Natural.topAmbient (R.outerOmegaConstantAxis N)
            (binaryCoordinateProductSpan
              (R.innerOmegaNaturalAxis N).toSubmodule
              (R.outerOmegaPairSumAxis N).toSubmodule)
            (R.omegaAxes_productSpan_le N)) :=
  (Coupled.towerCoupledHeadData R).
    omegaCoupledQuotientRepresentation_invariants_finrank_eq
      Natural.topAmbient_full N

/-- The generated cap-four table now bounds three literal representation
rows: the K and W invariant-form heads and the fixed residual L quotient. -/
theorem omegaRepresentationRows_le_four
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization Shared.top1 p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal}) :
    Module.finrank (ZMod 2)
        ((R.innerOmegaNaturalAxis N).toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod 2) Natural.Top (ZMod 2))) +
      Module.finrank (ZMod 2)
        ((R.outerOmegaPairSumAxis N).toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod 2) Natural.Top (ZMod 2))) +
      Module.finrank (ZMod 2)
        (OmegaCoupledQuotientRepresentation R N).invariants ≤ 4 := by
  rw [← (Coupled.towerCoupledHeadData R).
    omegaHeadDemand_eq_head_add_head_add_fixed
      Natural.topAmbient_full N]
  exact omegaHeadDemand_le_four R N

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

/-- The first concrete nonfixed-row split: socle multiplicity is bounded
by the literal kernel and inner image of the omega projection. -/
theorem omegaSocle_schurSocleMultiplicity_le_projectionKernel_add_inner
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization Shared.top1 p)
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
          (A := ((R.innerOmegaSubrepresentation N).toRepresentation.comp
            (R.rawQuotientMap N)).asModule) (X := X) := by
  rw [R.omegaSocle_schurSocleMultiplicity_eq_rawOmega N X]
  exact representationSchurMultiplicity_le_kernel_add_target
    (binaryKernelOmegaConjugationRepresentation (R.rawQuotientMap N))
    ((R.innerOmegaSubrepresentation N).toRepresentation.comp
      (R.rawQuotientMap N))
    (R.rawKernelOmegaInnerImageIntertwiner N)
    (R.rawKernelOmegaInnerImageIntertwiner_surjective N)

/-- Over the actual first pair top, every nonfixed simple row in the retained
outer quotient costs at most two Schur dimensions.  The exact pair-sum map
splits it into two nested quotients of paired-eight states, each covered by
the uniform finite quotient theorem. -/
theorem outerNestedQuotient_nonfixed_schurSocleMultiplicity_le_two_mul
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization Shared.top1 p)
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
  let tau := nestedQuotientRepresentation
    (R.frame.normalTopPermutationSubrepresentation N.1)
    (R.outerOmegaAxis N)
    (R.outerNormalAxis_le_outerOmegaAxis N)
  let q := R.outerNestedQuotientPairSumMap N
  let K := nestedQuotientRepresentation
    (R.outerNormalConstantPullbackAxis N)
    (R.outerOmegaConstantPullbackAxis N)
    (R.outerNormalConstant_le_outerOmegaConstant N)
  let T := nestedQuotientRepresentation
    (R.outerNormalPairSumPullbackAxis N)
    (R.outerOmegaPairSumPullbackAxis N)
    (R.outerNormalPairSum_le_outerOmegaPairSum N)
  letI : FiniteDimensional (ZMod 2) X :=
    Module.Finite.of_finite (ZMod 2) X
  have hKliteral :=
    QuotientGenerators.subrepresentationQuotient_comp_nonfixed_le_end_finrank
      R.outerTopToLiteral R.outerTopToLiteral_surjective
      (R.outerNormalConstantAxis N) (R.outerOmegaConstantAxis N)
      (R.outerNormalConstantAxis_le_outerOmegaConstantAxis N)
      sigma X hnonfixed
  have hTliteral :=
    QuotientGenerators.subrepresentationQuotient_comp_nonfixed_le_end_finrank
      R.outerTopToLiteral R.outerTopToLiteral_surjective
      (R.outerNormalPairSumAxis N) (R.outerOmegaPairSumAxis N)
      (R.outerNormalPairSumAxis_le_outerOmegaPairSumAxis N)
      sigma X hnonfixed
  have hKequiv : schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[R.frame.top.range])
        (A := K.asModule) (X := X) =
      schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[R.frame.top.range])
        (A := (q.ker.toRepresentation).asModule) (X := X) :=
    schurSocleMultiplicity_eq_of_representationEquiv
      K q.ker.toRepresentation
      (R.outerNestedQuotientPairSumKernelEquiv N)
  have hKsub : schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[R.frame.top.range])
        (A := q.ker.toRepresentation.asModule) (X := X) =
      schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[R.frame.top.range])
        (A := q.ker.asSubmodule) (X := X) :=
    schurSocleMultiplicity_eq_of_target_linearEquiv
      (submoduleRepresentationModuleEquiv tau q.ker.asSubmodule)
  have hKtransport : schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[R.frame.top.range])
        (A := K.asModule) (X := X) =
      schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[R.frame.top.range])
        (A := ((nestedQuotientRepresentation
          (R.outerNormalConstantAxis N)
          (R.outerOmegaConstantAxis N)
          (R.outerNormalConstantAxis_le_outerOmegaConstantAxis N)).comp
            R.outerTopToLiteral).asModule) (X := X) :=
    schurSocleMultiplicity_eq_of_representationEquiv
      K _ (R.outerConstantQuotientEquiv N)
  have hTtransport : schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[R.frame.top.range])
        (A := T.asModule) (X := X) =
      schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[R.frame.top.range])
        (A := ((nestedQuotientRepresentation
          (R.outerNormalPairSumAxis N)
          (R.outerOmegaPairSumAxis N)
          (R.outerNormalPairSumAxis_le_outerOmegaPairSumAxis N)).comp
            R.outerTopToLiteral).asModule) (X := X) :=
    schurSocleMultiplicity_eq_of_representationEquiv
      T _ (R.outerPairSumQuotientEquiv N)
  have hK : schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[R.frame.top.range])
        (A := q.ker.asSubmodule) (X := X) ≤
      Module.finrank (Module.End (ZMod 2)[R.frame.top.range] X) X := by
    rw [← hKsub, ← hKequiv, hKtransport]
    exact hKliteral
  have hT : schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[R.frame.top.range])
        (A := T.asModule) (X := X) ≤
      Module.finrank (Module.End (ZMod 2)[R.frame.top.range] X) X := by
    rw [hTtransport]
    exact hTliteral
  have hsplit := representationSchurMultiplicity_le_kernel_add_target
    tau T q (R.outerNestedQuotientPairSumMap_surjective N) (X := X)
  exact hsplit.trans (by omega)

/-- The same two-layer estimate after pullback along any surjective action
map onto the first pair top.  This is the form used after inflating the
physical outer kernel back to the original action. -/
theorem outerNestedQuotient_comp_nonfixed_le_two_mul
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization Shared.top1 p)
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
        (A := ((nestedQuotientRepresentation
          (R.frame.normalTopPermutationSubrepresentation N.1)
          (R.outerOmegaAxis N)
          (R.outerNormalAxis_le_outerOmegaAxis N)).comp gamma).asModule)
        (X := X) ≤
      2 * Module.finrank (Module.End (ZMod 2)[H] X) X := by
  let tau := nestedQuotientRepresentation
    (R.frame.normalTopPermutationSubrepresentation N.1)
    (R.outerOmegaAxis N)
    (R.outerNormalAxis_le_outerOmegaAxis N)
  let q0 := R.outerNestedQuotientPairSumMap N
  let K := nestedQuotientRepresentation
    (R.outerNormalConstantPullbackAxis N)
    (R.outerOmegaConstantPullbackAxis N)
    (R.outerNormalConstant_le_outerOmegaConstant N)
  let T := nestedQuotientRepresentation
    (R.outerNormalPairSumPullbackAxis N)
    (R.outerOmegaPairSumPullbackAxis N)
    (R.outerNormalPairSum_le_outerOmegaPairSum N)
  let q : (tau.comp gamma).IntertwiningMap (T.comp gamma) :=
    { toLinearMap := q0.toLinearMap
      isIntertwining' h := q0.isIntertwining' (gamma h) }
  let eK0 := R.outerNestedQuotientPairSumKernelEquiv N
  let eK : (K.comp gamma).Equiv q.ker.toRepresentation :=
    Representation.Equiv.mk eK0.toLinearEquiv (by
      intro h
      exact eK0.isIntertwining' (gamma h))
  let eT0 := R.outerPairSumQuotientEquiv N
  let eT : (T.comp gamma).Equiv
      ((nestedQuotientRepresentation
        (R.outerNormalPairSumAxis N)
        (R.outerOmegaPairSumAxis N)
        (R.outerNormalPairSumAxis_le_outerOmegaPairSumAxis N)).comp
          (R.outerTopToLiteral.comp gamma)) :=
    Representation.Equiv.mk eT0.toLinearEquiv (by
      intro h
      exact eT0.isIntertwining' (gamma h))
  let eKlit0 := R.outerConstantQuotientEquiv N
  let eKlit : (K.comp gamma).Equiv
      ((nestedQuotientRepresentation
        (R.outerNormalConstantAxis N)
        (R.outerOmegaConstantAxis N)
        (R.outerNormalConstantAxis_le_outerOmegaConstantAxis N)).comp
          (R.outerTopToLiteral.comp gamma)) :=
    Representation.Equiv.mk eKlit0.toLinearEquiv (by
      intro h
      exact eKlit0.isIntertwining' (gamma h))
  letI : FiniteDimensional (ZMod 2) X :=
    Module.Finite.of_finite (ZMod 2) X
  have hfinal : Function.Surjective (R.outerTopToLiteral.comp gamma) :=
    R.outerTopToLiteral_surjective.comp hgamma
  have hKliteral :=
    QuotientGenerators.subrepresentationQuotient_comp_nonfixed_le_end_finrank
      (R.outerTopToLiteral.comp gamma) hfinal
      (R.outerNormalConstantAxis N) (R.outerOmegaConstantAxis N)
      (R.outerNormalConstantAxis_le_outerOmegaConstantAxis N)
      sigma X hnonfixed
  have hTliteral :=
    QuotientGenerators.subrepresentationQuotient_comp_nonfixed_le_end_finrank
      (R.outerTopToLiteral.comp gamma) hfinal
      (R.outerNormalPairSumAxis N) (R.outerOmegaPairSumAxis N)
      (R.outerNormalPairSumAxis_le_outerOmegaPairSumAxis N)
      sigma X hnonfixed
  have hKsub : schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[H])
        (A := q.ker.toRepresentation.asModule) (X := X) =
      schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[H])
        (A := q.ker.asSubmodule) (X := X) :=
    schurSocleMultiplicity_eq_of_target_linearEquiv
      (submoduleRepresentationModuleEquiv (tau.comp gamma) q.ker.asSubmodule)
  have hK : schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[H])
        (A := q.ker.asSubmodule) (X := X) ≤
      Module.finrank (Module.End (ZMod 2)[H] X) X := by
    rw [← hKsub,
      ← schurSocleMultiplicity_eq_of_representationEquiv
        (K.comp gamma) q.ker.toRepresentation eK,
      schurSocleMultiplicity_eq_of_representationEquiv
        (K.comp gamma) _ eKlit]
    exact hKliteral
  have hT : schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[H])
        (A := (T.comp gamma).asModule) (X := X) ≤
      Module.finrank (Module.End (ZMod 2)[H] X) X := by
    rw [schurSocleMultiplicity_eq_of_representationEquiv
      (T.comp gamma) _ eT]
    exact hTliteral
  have hq : Function.Surjective q :=
    R.outerNestedQuotientPairSumMap_surjective N
  have hsplit := representationSchurMultiplicity_le_kernel_add_target
    (tau.comp gamma) (T.comp gamma) q hq (X := X)
  exact hsplit.trans (by omega)

/-- Every nonfixed simple row in the actual inner omega image costs one
Schur dimension.  The ordinary state quotients use the cyclic-dual table;
the unique exceptional quotient is a binary plane. -/
theorem innerOmega_nonfixed_schurSocleMultiplicity_le_end_finrank
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization Shared.top1 p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal})
    (X : Submodule (ZMod 2)[preE7PairAction 16 p ⧸ N.1]
      (OmegaSocleRepresentation R N).asModule)
    [IsSimpleModule (ZMod 2)[preE7PairAction 16 p ⧸ N.1] X]
    (hnonfixed : ¬ representationSubmoduleFixed
      (OmegaSocleRepresentation R N) X) :
    schurSocleMultiplicity
        (k := ZMod 2)
        (R := (ZMod 2)[preE7PairAction 16 p ⧸ N.1])
        (A := ((R.innerOmegaSubrepresentation N).toRepresentation.comp
          (R.rawQuotientMap N)).asModule) (X := X) ≤
      Module.finrank
        (Module.End (ZMod 2)[preE7PairAction 16 p ⧸ N.1] X) X := by
  let A := R.moduleAxis N
  let B := R.innerOmegaNaturalAxis N
  let hAB := R.moduleAxis_le_innerOmegaNaturalAxis N
  obtain ⟨i, hi⟩ := Natural.registry.complete A
  obtain ⟨j, hj⟩ := Natural.registry.complete B
  subst A
  subst B
  let tau := nestedQuotientRepresentation
    (Natural.states i) (Natural.states j) hAB
  let sigma := (R.innerOmegaSubrepresentation N).toRepresentation
  let q := QuotientGroup.mk' (R.topNormal N.1)
  let E : tau.Equiv (sigma.comp q) :=
    R.innerNestedQuotientEquivInnerOmegaInflation N
  letI : FiniteDimensional (ZMod 2) X :=
    Module.Finite.of_finite (ZMod 2) X
  by_cases hexception : i = 4 ∧ j = 8
  · obtain ⟨rfl, rfl⟩ := hexception
    have htau : Module.finrank (ZMod 2) tau.asModule ≤ 2 := by
      simpa only [tau] using QuotientGenerators.exceptional_finrank_le_two hAB
    have htarget : Module.finrank (ZMod 2)
        ((sigma.comp (R.rawQuotientMap N)).asModule) ≤ 2 := by
      have hE := E.toLinearEquiv.finrank_eq
      have hsigma : Module.finrank (ZMod 2) sigma.asModule ≤ 2 := by
        rw [← hE]
        exact htau
      simpa only [sigma] using hsigma
    exact schurSocleMultiplicity_le_one_of_finrank_le_two_of_nonfixed
      (OmegaSocleRepresentation R N) X hnonfixed htarget
  · have hgen : RepresentationGeneratedBy tau.dual 1 := by
      simpa only [tau] using
        QuotientGenerators.nestedQuotient_dual_generated i j hAB hexception
    have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
    have hcapSigma : representationSchurCapacity sigma ≤ 1 :=
      representationSchurCapacity_le_of_comp_equiv_dual_generated
        tau sigma q hq E 1 hgen
    have hcap : representationSchurCapacity
        (sigma.comp (R.rawQuotientMap N)) ≤ 1 := by
      rw [representationSchurCapacity_comp (R.rawQuotientMap N)
        (R.rawQuotientMap_surjective N)]
      exact hcapSigma
    simpa only [sigma, one_mul] using
      (schurSocleMultiplicity_le_nat_mul_end_finrank_of_capacity_le
        (sigma.comp (R.rawQuotientMap N)) 1 hcap (X := X))

/-- Every nonfixed simple row in the physical outer projection kernel costs
two Schur dimensions.  The proof inflates the actual kernel and simple row
back to the original action, uses the action-level identification with
`B/A`, applies the two endpoint quotient theorem, and descends the resulting
multiplicity unchanged. -/
theorem outerOmega_nonfixed_schurSocleMultiplicity_le_two_mul_end_finrank
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization Shared.top1 p)
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
  let Q := preE7PairAction 16 p ⧸ N.1
  let G := preE7PairAction 16 p
  let gamma : G →* Q := QuotientGroup.mk' N.1
  have hgamma : Function.Surjective gamma := QuotientGroup.mk'_surjective _
  let omega := OmegaSocleRepresentation R N
  let outer := (R.rawKernelOmegaInnerImageIntertwiner N).ker.toRepresentation
  let rhoX := (Subrepresentation.ofSubmodule' X).toRepresentation
  let sigmaG := omega.comp gamma
  let XG := representationInflatedSubmodule gamma hgamma omega X
  letI : FiniteDimensional (ZMod 2) X :=
    Module.Finite.of_finite (ZMod 2) X
  letI : IsSimpleModule (ZMod 2)[Q] rhoX.asModule := by
    exact IsSimpleModule.congr
      (submoduleRepresentationModuleEquiv omega X)
  letI : IsSimpleModule (ZMod 2)[G] (rhoX.comp gamma).asModule :=
    representation_comp_isSimpleModule gamma hgamma rhoX
  letI : IsSimpleModule (ZMod 2)[G] XG :=
    representationInflatedSubmodule_isSimple gamma hgamma omega X
  letI : FiniteDimensional (ZMod 2) XG :=
    FiniteDimensional.of_injective
      (XG.subtype.restrictScalars (ZMod 2)) XG.subtype_injective
  have hnonfixedG : ¬ representationSubmoduleFixed sigmaG XG := by
    intro hfixed
    exact hnonfixed
      ((representationInflatedSubmodule_fixed_iff
        gamma hgamma omega X).1 hfixed)
  have hcoord := outerNestedQuotient_comp_nonfixed_le_two_mul
    R N R.frame.top.rangeRestrict R.frame.top.rangeRestrict_surjective
    sigmaG XG hnonfixedG
  let tau := nestedQuotientRepresentation
    (R.frame.normalTopPermutationSubrepresentation N.1)
    (R.outerOmegaAxis N)
    (R.outerNormalAxis_le_outerOmegaAxis N)
  let eOuter := R.rawKernelOmegaOuterInflationEquivNestedQuotient N
  have htarget : schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[G])
        (A := (outer.comp gamma).asModule) (X := XG) =
      schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[G])
        (A := (tau.comp R.frame.top.rangeRestrict).asModule) (X := XG) :=
    schurSocleMultiplicity_eq_of_representationEquiv
      (outer.comp gamma) (tau.comp R.frame.top.rangeRestrict) eOuter
  have hphysicalG : schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[G])
        (A := (outer.comp gamma).asModule) (X := XG) ≤
      2 * Module.finrank (Module.End (ZMod 2)[G] XG) XG := by
    rw [htarget]
    exact hcoord
  let eXrep := representationInflatedSubmoduleEquiv
    gamma hgamma omega X
  let eXmodule : (rhoX.comp gamma).asModule ≃ₗ[(ZMod 2)[G]] XG :=
    (representationEquivLinearEquivAsModule
      (rhoX.comp gamma)
      (Subrepresentation.ofSubmodule' XG).toRepresentation
      eXrep).trans
        (submoduleRepresentationModuleEquiv sigmaG XG)
  have hsourceG : schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[G])
        (A := (outer.comp gamma).asModule)
        (X := (rhoX.comp gamma).asModule) =
      schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[G])
        (A := (outer.comp gamma).asModule) (X := XG) :=
    schurSocleMultiplicity_eq_of_source_linearEquiv eXmodule
  have hinflate := schurSocleMultiplicity_comp_eq_representation
    gamma hgamma rhoX outer
  have hsourceQ : schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[Q])
        (A := outer.asModule) (X := rhoX.asModule) =
      schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[Q])
        (A := outer.asModule) (X := X) :=
    schurSocleMultiplicity_eq_of_source_linearEquiv
      (submoduleRepresentationModuleEquiv omega X)
  have htargetQ : schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[Q])
        (A := outer.asModule) (X := X) =
      schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[Q])
        (A := (R.rawKernelOmegaInnerImageIntertwiner N).ker.asSubmodule)
        (X := X) :=
    schurSocleMultiplicity_eq_of_target_linearEquiv
      (submoduleRepresentationModuleEquiv
        (binaryKernelOmegaConjugationRepresentation
          (R.rawQuotientMap N))
        (R.rawKernelOmegaInnerImageIntertwiner N).ker.asSubmodule)
  have hendG := moduleFinrankOverEnd_eq_of_linearEquiv eXmodule
  have hendInflate := representationFinrankOverEnd_comp_eq
    gamma hgamma rhoX
  have hendQ := moduleFinrankOverEnd_eq_of_linearEquiv
    (submoduleRepresentationModuleEquiv omega X)
  have hend : Module.finrank (Module.End (ZMod 2)[G] XG) XG =
      Module.finrank (Module.End (ZMod 2)[Q] X) X :=
    hendG.symm.trans (hendInflate.trans hendQ)
  rw [← hsourceG, hinflate, hsourceQ, htargetQ, hend] at hphysicalG
  simpa only [outer, Q] using hphysicalG

/-- The physical outer and inner estimates close the complete nonfixed row
of the omega socle with the required coefficient three. -/
theorem omegaSocle_nonfixed_schurSocleMultiplicity_le_three_mul_end_finrank
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization Shared.top1 p)
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
  have hsplit :=
    omegaSocle_schurSocleMultiplicity_le_projectionKernel_add_inner
      R N X
  have houter :=
    outerOmega_nonfixed_schurSocleMultiplicity_le_two_mul_end_finrank
      R N X hnonfixed
  have hinner := innerOmega_nonfixed_schurSocleMultiplicity_le_end_finrank
    R N X hnonfixed
  exact hsplit.trans (by omega)

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

/-- Assemble the all-normal capacity theorem directly from the two
remaining representation inequalities.  This keeps the unresolved
boundary on the raw omega filtration and on literal nonfixed simple rows,
rather than on a project-defined capacity predicate. -/
theorem omegaSocleSchurCapacityLeFour_of_rawCoupled_nonfixed
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization Shared.top1 p)
    (hraw : ∀ N,
      Module.finrank (ZMod 2)
          (binaryKernelOmegaConjugationRepresentation
            (R.rawQuotientMap N)).invariants ≤
        (Coupled.towerCoupledHeadData R).omegaHeadDemand N)
    (hnonfixed : ∀ N
      (X : Submodule (ZMod 2)[preE7PairAction 16 p ⫽ N.1]
        (OmegaSocleRepresentation R N).asModule),
      [IsSimpleModule (ZMod 2)[preE7PairAction 16 p ⫽ N.1] X] →
      ¬ representationSubmoduleFixed (OmegaSocleRepresentation R N) X →
      schurSocleMultiplicity
          (k := ZMod 2)
          (R := (ZMod 2)[preE7PairAction 16 p ⫽ N.1])
          (A := (OmegaSocleRepresentation R N).asModule) (X := X) ≤
        3 * Module.finrank
          (Module.End (ZMod 2)[preE7PairAction 16 p ⫽ N.1] X) X) :
    OmegaSocleSchurCapacityLeFour R := by
  intro N
  apply omegaSocle_schurCapacity_le_four_of_coupled_nonfixed R N
  · exact R.omegaSocle_invariants_le_of_rawOmega N (hraw N)
  · exact hnonfixed N

/-- After the physical outer and inner layer theorems, the coupled raw fixed
inequality is the sole remaining input for the all-normal cap-four result. -/
theorem omegaSocleSchurCapacityLeFour_of_rawCoupled
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopTowerRealization Shared.top1 p)
    (hraw : ∀ N,
      Module.finrank (ZMod 2)
          (binaryKernelOmegaConjugationRepresentation
            (R.rawQuotientMap N)).invariants ≤
        (Coupled.towerCoupledHeadData R).omegaHeadDemand N) :
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
    (R : DegreeTwoPairTopTowerRealization Shared.top1 p) :
    OmegaSocleSchurCapacityLeFour R := by
  intro N
  apply representationSchurCapacity_le_of_fixed_nonfixed_multiplicity
    (OmegaSocleRepresentation R N) 4
  · rw [R.omegaSocle_invariants_finrank_eq_rawOmega N]
    exact (Coupled.towerCoupledHeadData R).
      rawKernelOmega_invariants_finrank_le N
  · intro X _hX hnonfixed
    have hthree :=
      omegaSocle_nonfixed_schurSocleMultiplicity_le_three_mul_end_finrank
        R N X hnonfixed
    exact hthree.trans (by omega)

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
