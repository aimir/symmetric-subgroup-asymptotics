import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopTowerCoupledHeads
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopTowerNestedQuotient
import SymmetricSubgroupAsymptotics.DualGeneratorSchurCapacity
import SymmetricSubgroupAsymptotics.FiniteSelfDualNestedQuotientGenerator
import SymmetricSubgroupAsymptotics.Non2SchurRowDegrees
import SymmetricSubgroupAsymptotics.PermutationFunctionSelfDual

/-!
# Finite nested-quotient generator declarations for pair tops

The nonfixed part of a two-frame omega filtration uses only one finite fact
about the literal natural module: every nested invariant quotient either has
cyclic dual or has binary dimension at most two.  Both alternatives imply
the same one-Schur-dimension bound after inflation along any surjective top
map.
-/

-- Lean 4.30's suggestion-index exporter traverses the fully dependent
-- signatures in this namespace for minutes after elaboration. Exclude them
-- from automatic premise suggestions; all declarations are still checked
-- and exported normally, and remain available by name.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "DegreeTwoPairTopNestedQuotientGeneratorData"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

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

/-- Realization-free finite generator certificate for every nested quotient
of the literal natural permutation module. -/
structure DegreeTwoPairTopNestedQuotientGeneratorData
    {t : ℕ} (D : DegreeTwoPairTopFiniteInterface t) : Prop where
  certificate : ∀
    (A B : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin t)))
    (hAB : A ≤ B),
    RepresentationGeneratedBy
        (nestedQuotientRepresentation A B hAB).dual 1 ∨
      Module.finrank (ZMod 2)
        (nestedQuotientRepresentation A B hAB).asModule ≤ 2

/-- Build the pair-top declaration from a compact self-dual finite-state
table exported beside the natural-module registry. -/
noncomputable def DegreeTwoPairTopNestedQuotientGeneratorData.ofFiniteTable
    {t s : ℕ} (D : DegreeTwoPairTopFiniteInterface t)
    (states : Fin s → Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin t)))
    (registry : BinaryInvariantCyclicOrbitRegistry
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin t)) states)
    (table : FiniteSelfDualNestedQuotientGeneratorData registry
      (permutationFunctionRepresentationSelfDual
        (k := ZMod 2) (G := D.top) (X := Fin t))) :
    DegreeTwoPairTopNestedQuotientGeneratorData D where
  certificate := table.subrepresentationQuotient_generated_or_finrank_le_two
    registry
    (permutationFunctionRepresentationSelfDual
      (k := ZMod 2) (G := D.top) (X := Fin t))

namespace DegreeTwoPairTopNestedQuotientGeneratorData

variable {t : ℕ} {D : DegreeTwoPairTopFiniteInterface t}
  (Q : DegreeTwoPairTopNestedQuotientGeneratorData D)

include Q

/-- The finite generator declaration gives the uniform nonfixed bound after
pullback along any surjective action map. -/
theorem subrepresentationQuotient_comp_nonfixed_le_end_finrank
    {H X : Type} [Group H]
    (gamma : H →* D.top) (hgamma : Function.Surjective gamma)
    (A B : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin t)))
    (hAB : A ≤ B)
    [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (sigma : Representation (ZMod 2) H X)
    (S : Submodule (ZMod 2)[H] sigma.asModule)
    [Finite S] [IsSimpleModule (ZMod 2)[H] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S) :
    schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[H])
        (A := (inflatedRepresentation gamma (nestedQuotientRepresentation A B hAB)).asModule)
        (X := S) ≤
      Module.finrank (Module.End (ZMod 2)[H] S) S := by
  letI : FiniteDimensional (ZMod 2) X :=
    Module.Finite.of_finite
  letI : FiniteDimensional (ZMod 2) S :=
    Module.Finite.of_finite
  have hcertificate := Q.certificate A B hAB
  rcases hcertificate with hgen | hsmall
  · let tau := nestedQuotientRepresentation A B hAB
    have hgenComp : RepresentationGeneratedBy (inflatedRepresentation gamma tau.dual) 1 :=
      RepresentationGeneratedBy.comp_of_surjective
        tau.dual gamma hgamma hgen
    let E := representationDualCompEquiv tau gamma
    have hdual : RepresentationGeneratedBy (inflatedRepresentation gamma tau).dual 1 :=
      representationGeneratedBy_of_surjective
        (inflatedRepresentation gamma tau.dual) (inflatedRepresentation gamma tau).dual
        E.symm.toIntertwiningMap E.symm.surjective hgenComp
    have hschur := schurSocleMultiplicity_le_of_dual_generated
      (inflatedRepresentation gamma tau) 1 hdual (X := S)
    simpa only [tau, one_mul] using hschur
  · have hone : schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[H])
        (A := (inflatedRepresentation gamma (nestedQuotientRepresentation A B hAB)).asModule)
        (X := S) ≤ 1 :=
      schurSocleMultiplicity_le_one_of_finrank_le_two_of_nonfixed
        sigma S hnonfixed hsmall
    have hpos : 0 < Module.finrank (Module.End (ZMod 2)[H] S) S := by
      letI : Nontrivial S := IsSimpleModule.nontrivial (ZMod 2)[H] S
      have hdim := Module.finrank_pos (R := ZMod 2) (M := S)
      have htower := schur_simple_finrank_tower
        (k := ZMod 2) (R := (ZMod 2)[H]) (X := S)
      exact Nat.pos_of_mul_pos_left (htower ▸ hdim)
    exact hone.trans hpos

/-! ## Physical two-frame consequences -/

variable {p : PreE7PairActionClass 16}

local instance innerOmegaFinite
    (R : DegreeTwoPairTopTowerRealization D p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal}) :
    Finite (R.innerOmegaSubrepresentation N).toSubmodule :=
  Finite.of_surjective _ (R.rawKernelOmegaInnerImageIntertwiner_surjective N)

local instance innerOmegaFiniteDimensional
    (R : DegreeTwoPairTopTowerRealization D p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal}) :
    FiniteDimensional (ZMod 2) (R.innerOmegaSubrepresentation N).toSubmodule :=
  Module.Finite.of_finite

/-- Canonical socle of the direct-kernel omega representation. -/
abbrev omegaSocleRepresentation
    (_Q : DegreeTwoPairTopNestedQuotientGeneratorData D)
    (R : DegreeTwoPairTopTowerRealization D p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal}) :=
  (finiteRepresentationSocle
    (binaryKernelOmegaConjugationRepresentation
      (R.rawQuotientMap N))).toRepresentation

theorem omegaSocle_invariants_finrank_eq_rawOmega
    (R : DegreeTwoPairTopTowerRealization D p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal}) :
    Module.finrank (ZMod 2)
        (Q.omegaSocleRepresentation R N).invariants =
      Module.finrank (ZMod 2)
        (binaryKernelOmegaConjugationRepresentation
          (R.rawQuotientMap N)).invariants :=
  finiteRepresentationSocle_invariants_finrank_eq
    (binaryKernelOmegaConjugationRepresentation (R.rawQuotientMap N))

theorem omegaSocle_schurSocleMultiplicity_eq_rawOmega
    (R : DegreeTwoPairTopTowerRealization D p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal})
    (X : Submodule (ZMod 2)[preE7PairAction 16 p ⧸ N.1]
      (Q.omegaSocleRepresentation R N).asModule)
    [IsSimpleModule (ZMod 2)[preE7PairAction 16 p ⧸ N.1] X] :
    schurSocleMultiplicity
        (k := ZMod 2)
        (R := (ZMod 2)[preE7PairAction 16 p ⧸ N.1])
        (A := (Q.omegaSocleRepresentation R N).asModule) (X := X) =
      schurSocleMultiplicity
        (k := ZMod 2)
        (R := (ZMod 2)[preE7PairAction 16 p ⧸ N.1])
        (A := (binaryKernelOmegaConjugationRepresentation
          (R.rawQuotientMap N)).asModule) (X := X) :=
  finiteRepresentationSocle_schurSocleMultiplicity_eq
    (binaryKernelOmegaConjugationRepresentation (R.rawQuotientMap N))

theorem omegaSocle_schurSocleMultiplicity_le_projectionKernel_add_inner
    (R : DegreeTwoPairTopTowerRealization D p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal})
    (X : Submodule (ZMod 2)[preE7PairAction 16 p ⧸ N.1]
      (Q.omegaSocleRepresentation R N).asModule)
    [IsSimpleModule (ZMod 2)[preE7PairAction 16 p ⧸ N.1] X] :
    schurSocleMultiplicity
        (k := ZMod 2)
        (R := (ZMod 2)[preE7PairAction 16 p ⧸ N.1])
        (A := (Q.omegaSocleRepresentation R N).asModule) (X := X) ≤
      schurSocleMultiplicity
          (k := ZMod 2)
          (R := (ZMod 2)[preE7PairAction 16 p ⧸ N.1])
          (A := (R.rawKernelOmegaInnerImageIntertwiner N).ker.asSubmodule)
          (X := X) +
        schurSocleMultiplicity
          (k := ZMod 2)
          (R := (ZMod 2)[preE7PairAction 16 p ⧸ N.1])
          (A := (inflatedRepresentation (R.rawQuotientMap N) (R.innerOmegaSubrepresentation N).toRepresentation).asModule) (X := X) := by
  apply (Q.omegaSocle_schurSocleMultiplicity_eq_rawOmega R N X).trans_le
  exact representationSchurMultiplicity_le_kernel_add_target
    (binaryKernelOmegaConjugationRepresentation (R.rawQuotientMap N))
    (inflatedRepresentation (R.rawQuotientMap N) (R.innerOmegaSubrepresentation N).toRepresentation)
    (R.rawKernelOmegaInnerImageIntertwiner N)
    (R.rawKernelOmegaInnerImageIntertwiner_surjective N)

/-- The two fixed first-frame endpoints each cost one nonfixed Schur
dimension after arbitrary inflation. -/
theorem outerNestedQuotient_comp_nonfixed_le_two_mul
    (R : DegreeTwoPairTopTowerRealization D p)
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
  let q : (inflatedRepresentation gamma tau).IntertwiningMap (inflatedRepresentation gamma T) :=
    { toLinearMap := q0.toLinearMap
      isIntertwining' h := q0.isIntertwining' (gamma h) }
  let eK0 := R.outerNestedQuotientPairSumKernelEquiv N
  let eK : (inflatedRepresentation gamma K).Equiv q.ker.toRepresentation :=
    Representation.Equiv.mk eK0.toLinearEquiv (by
      intro h
      exact eK0.isIntertwining' (gamma h))
  let eT0 := R.outerPairSumQuotientEquiv N
  let eT : (inflatedRepresentation gamma T).Equiv
      (inflatedRepresentation (R.outerTopToLiteral.comp gamma) (nestedQuotientRepresentation
        (R.outerNormalPairSumAxis N)
        (R.outerOmegaPairSumAxis N)
        (R.outerNormalPairSumAxis_le_outerOmegaPairSumAxis N))) :=
    Representation.Equiv.mk eT0.toLinearEquiv (by
      intro h
      exact eT0.isIntertwining' (gamma h))
  let eKlit0 := R.outerConstantQuotientEquiv N
  let eKlit : (inflatedRepresentation gamma K).Equiv
      (inflatedRepresentation (R.outerTopToLiteral.comp gamma) (nestedQuotientRepresentation
        (R.outerNormalConstantAxis N)
        (R.outerOmegaConstantAxis N)
        (R.outerNormalConstantAxis_le_outerOmegaConstantAxis N))) :=
    Representation.Equiv.mk eKlit0.toLinearEquiv (by
      intro h
      exact eKlit0.isIntertwining' (gamma h))
  letI : FiniteDimensional (ZMod 2) X :=
    Module.Finite.of_finite
  have hfinal : Function.Surjective (R.outerTopToLiteral.comp gamma) :=
    R.outerTopToLiteral_surjective.comp hgamma
  have hKliteral := Q.subrepresentationQuotient_comp_nonfixed_le_end_finrank
    (R.outerTopToLiteral.comp gamma) hfinal
    (R.outerNormalConstantAxis N) (R.outerOmegaConstantAxis N)
    (R.outerNormalConstantAxis_le_outerOmegaConstantAxis N)
    sigma X hnonfixed
  have hTliteral := Q.subrepresentationQuotient_comp_nonfixed_le_end_finrank
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
      (submoduleRepresentationModuleEquiv (inflatedRepresentation gamma tau) q.ker.asSubmodule).symm
  have hK : schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[H])
        (A := q.ker.asSubmodule) (X := X) ≤
      Module.finrank (Module.End (ZMod 2)[H] X) X := by
    have heK := schurSocleMultiplicity_eq_of_representationEquiv
      (X := X) (inflatedRepresentation gamma K) q.ker.toRepresentation eK
    have heKlit := schurSocleMultiplicity_eq_of_representationEquiv
      (X := X) (inflatedRepresentation gamma K) _ eKlit
    exact (hKsub.symm.trans (heK.symm.trans heKlit)).trans_le hKliteral
  have hT : schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[H])
        (A := (inflatedRepresentation gamma T).asModule) (X := X) ≤
      Module.finrank (Module.End (ZMod 2)[H] X) X := by
    exact (schurSocleMultiplicity_eq_of_representationEquiv
      (X := X) (inflatedRepresentation gamma T) _ eT).trans_le hTliteral
  have hq : Function.Surjective q :=
    R.outerNestedQuotientPairSumMap_surjective N
  have hsplit := representationSchurMultiplicity_le_kernel_add_target
    (inflatedRepresentation gamma tau) (inflatedRepresentation gamma T) q hq (X := X)
  exact hsplit.trans (by omega)

/-- The actual inner projection image costs one nonfixed Schur dimension. -/
theorem innerOmega_nonfixed_schurSocleMultiplicity_le_end_finrank
    (R : DegreeTwoPairTopTowerRealization D p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal})
    (X : Submodule (ZMod 2)[preE7PairAction 16 p ⧸ N.1]
      (Q.omegaSocleRepresentation R N).asModule)
    [IsSimpleModule (ZMod 2)[preE7PairAction 16 p ⧸ N.1] X]
    (hnonfixed : ¬ representationSubmoduleFixed
      (Q.omegaSocleRepresentation R N) X) :
    schurSocleMultiplicity
        (k := ZMod 2)
        (R := (ZMod 2)[preE7PairAction 16 p ⧸ N.1])
        (A := (inflatedRepresentation (R.rawQuotientMap N) (R.innerOmegaSubrepresentation N).toRepresentation).asModule) (X := X) ≤
      Module.finrank
        (Module.End (ZMod 2)[preE7PairAction 16 p ⧸ N.1] X) X := by
  let A := R.moduleAxis N
  let B := R.innerOmegaNaturalAxis N
  let hAB := R.moduleAxis_le_innerOmegaNaturalAxis N
  let tau := nestedQuotientRepresentation A B hAB
  let sigma := (R.innerOmegaSubrepresentation N).toRepresentation
  let q := QuotientGroup.mk' (R.topNormal N.1)
  let E : tau.Equiv (inflatedRepresentation q sigma) :=
    R.innerNestedQuotientEquivInnerOmegaInflation N
  letI : FiniteDimensional (ZMod 2) X :=
    Module.Finite.of_finite
  have hcertificate := Q.certificate A B hAB
  rcases hcertificate with hgen | hsmall
  · have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
    have hcapSigma : representationSchurCapacity sigma ≤ 1 := by
      simpa only [Nat.cast_one] using
        representationSchurCapacity_le_of_comp_equiv_dual_generated
          tau sigma q hq E 1 hgen
    have hcap : representationSchurCapacity
        (inflatedRepresentation (R.rawQuotientMap N) sigma) ≤ 1 := by
      exact (representationSchurCapacity_comp (R.rawQuotientMap N)
        (R.rawQuotientMap_surjective N) sigma).trans_le hcapSigma
    simpa only [sigma, one_mul] using
      (schurSocleMultiplicity_le_nat_mul_end_finrank_of_capacity_le
        (inflatedRepresentation (R.rawQuotientMap N) sigma) 1
        (by simpa only [Nat.cast_one] using hcap) (X := X))
  · have htarget : Module.finrank (ZMod 2)
        ((inflatedRepresentation (R.rawQuotientMap N) sigma).asModule) ≤ 2 := by
      have hE := E.toLinearEquiv.finrank_eq
      have hsigma : Module.finrank (ZMod 2) sigma.asModule ≤ 2 := by
        exact hE.symm.trans_le hsmall
      simpa only [sigma] using hsigma
    have hone := schurSocleMultiplicity_le_one_of_finrank_le_two_of_nonfixed
      (Q.omegaSocleRepresentation R N) X hnonfixed htarget
    have hpos : 0 < Module.finrank
        (Module.End (ZMod 2)[preE7PairAction 16 p ⧸ N.1] X) X := by
      letI : Nontrivial X :=
        IsSimpleModule.nontrivial (ZMod 2)[preE7PairAction 16 p ⧸ N.1] X
      have hdim := Module.finrank_pos (R := ZMod 2) (M := X)
      have htower := schur_simple_finrank_tower
        (k := ZMod 2) (R := (ZMod 2)[preE7PairAction 16 p ⧸ N.1]) (X := X)
      exact Nat.pos_of_mul_pos_left (htower ▸ hdim)
    exact hone.trans hpos

set_option maxHeartbeats 800000 in
/-- The physical outer projection kernel costs two nonfixed Schur
dimensions. -/
theorem outerOmega_nonfixed_schurSocleMultiplicity_le_two_mul_end_finrank
    (R : DegreeTwoPairTopTowerRealization D p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal})
    (X : Submodule (ZMod 2)[preE7PairAction 16 p ⧸ N.1]
      (Q.omegaSocleRepresentation R N).asModule)
    [IsSimpleModule (ZMod 2)[preE7PairAction 16 p ⧸ N.1] X]
    (hnonfixed : ¬ representationSubmoduleFixed
      (Q.omegaSocleRepresentation R N) X) :
    schurSocleMultiplicity
        (k := ZMod 2)
        (R := (ZMod 2)[preE7PairAction 16 p ⧸ N.1])
        (A := (R.rawKernelOmegaInnerImageIntertwiner N).ker.asSubmodule)
        (X := X) ≤
      2 * Module.finrank
        (Module.End (ZMod 2)[preE7PairAction 16 p ⧸ N.1] X) X := by
  let GQ := preE7PairAction 16 p ⧸ N.1
  let G := preE7PairAction 16 p
  let gamma : G →* GQ := QuotientGroup.mk' N.1
  have hgamma : Function.Surjective gamma := QuotientGroup.mk'_surjective _
  let omega := Q.omegaSocleRepresentation R N
  let outer := (R.rawKernelOmegaInnerImageIntertwiner N).ker.toRepresentation
  let rhoX := (Subrepresentation.ofSubmodule' X).toRepresentation
  let sigmaG := inflatedRepresentation gamma omega
  let XG := representationInflatedSubmodule gamma hgamma omega X
  letI : FiniteDimensional (ZMod 2) X :=
    Module.Finite.of_finite
  letI : IsSimpleModule (ZMod 2)[GQ] rhoX.asModule :=
    IsSimpleModule.congr (submoduleRepresentationModuleEquiv omega X).symm
  letI : IsSimpleModule (ZMod 2)[G] (inflatedRepresentation gamma rhoX).asModule :=
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
  have hcoord := Q.outerNestedQuotient_comp_nonfixed_le_two_mul
    R N R.frame.top.rangeRestrict R.frame.top.rangeRestrict_surjective
    sigmaG XG hnonfixedG
  let tau := nestedQuotientRepresentation
    (R.frame.normalTopPermutationSubrepresentation N.1)
    (R.outerOmegaAxis N)
    (R.outerNormalAxis_le_outerOmegaAxis N)
  let eOuter := R.rawKernelOmegaOuterInflationEquivNestedQuotient N
  have htarget : schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[G])
        (A := (inflatedRepresentation gamma outer).asModule) (X := XG) =
      schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[G])
        (A := (inflatedRepresentation R.frame.top.rangeRestrict tau).asModule) (X := XG) :=
    schurSocleMultiplicity_eq_of_representationEquiv
      (inflatedRepresentation gamma outer) (inflatedRepresentation R.frame.top.rangeRestrict tau) eOuter
  have hphysicalG : schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[G])
        (A := (inflatedRepresentation gamma outer).asModule) (X := XG) ≤
      2 * Module.finrank (Module.End (ZMod 2)[G] XG) XG := by
    exact htarget.trans_le hcoord
  let eXrep := representationInflatedSubmoduleEquiv
    gamma hgamma omega X
  let eXmodule : (inflatedRepresentation gamma rhoX).asModule ≃ₗ[(ZMod 2)[G]] XG :=
    (representationEquivLinearEquivAsModule
      (inflatedRepresentation gamma rhoX)
      (Subrepresentation.ofSubmodule' XG).toRepresentation
      eXrep).trans
        (submoduleRepresentationModuleEquiv sigmaG XG).symm
  have hsourceG : schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[G])
        (A := (inflatedRepresentation gamma outer).asModule)
        (X := (inflatedRepresentation gamma rhoX).asModule) =
      schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[G])
        (A := (inflatedRepresentation gamma outer).asModule) (X := XG) :=
    schurSocleMultiplicity_eq_of_source_linearEquiv eXmodule
  have hinflate := schurSocleMultiplicity_comp_eq_representation
    gamma hgamma rhoX outer
  have hsourceQ : schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[GQ])
        (A := outer.asModule) (X := rhoX.asModule) =
      schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[GQ])
        (A := outer.asModule) (X := X) :=
    schurSocleMultiplicity_eq_of_source_linearEquiv
      (submoduleRepresentationModuleEquiv omega X).symm
  have htargetQ : schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[GQ])
        (A := outer.asModule) (X := X) =
      schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[GQ])
        (A := (R.rawKernelOmegaInnerImageIntertwiner N).ker.asSubmodule)
        (X := X) :=
    schurSocleMultiplicity_eq_of_target_linearEquiv
      (submoduleRepresentationModuleEquiv
        (binaryKernelOmegaConjugationRepresentation
          (R.rawQuotientMap N))
        (R.rawKernelOmegaInnerImageIntertwiner N).ker.asSubmodule).symm
  have hendG := moduleFinrankOverEnd_eq_of_linearEquiv (k := ZMod 2) eXmodule
  have hendInflate := representationFinrankOverEnd_comp_eq
    gamma hgamma rhoX
  have hendQ := moduleFinrankOverEnd_eq_of_linearEquiv
    (k := ZMod 2) (R := (ZMod 2)[GQ]) (X := rhoX.asModule) (V := X)
    (submoduleRepresentationModuleEquiv omega X).symm
  have hend : Module.finrank (Module.End (ZMod 2)[G] XG) XG =
      Module.finrank (Module.End (ZMod 2)[GQ] X) X :=
    hendG.symm.trans (hendInflate.trans hendQ)
  have hleft := hsourceG.symm.trans
    (hinflate.trans (hsourceQ.trans htargetQ))
  have hright := congrArg (fun n : ℕ ↦ 2 * n) hend
  exact hleft.symm.trans_le (hphysicalG.trans_eq hright)

/-- The inner and outer pair sections give the uniform coefficient-three
bound for every nonfixed simple row. -/
theorem omegaSocle_nonfixed_schurSocleMultiplicity_le_three_mul_end_finrank
    (R : DegreeTwoPairTopTowerRealization D p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal})
    (X : Submodule (ZMod 2)[preE7PairAction 16 p ⧸ N.1]
      (Q.omegaSocleRepresentation R N).asModule)
    [IsSimpleModule (ZMod 2)[preE7PairAction 16 p ⧸ N.1] X]
    (hnonfixed : ¬ representationSubmoduleFixed
      (Q.omegaSocleRepresentation R N) X) :
    schurSocleMultiplicity
        (k := ZMod 2)
        (R := (ZMod 2)[preE7PairAction 16 p ⧸ N.1])
        (A := (Q.omegaSocleRepresentation R N).asModule) (X := X) ≤
      3 * Module.finrank
        (Module.End (ZMod 2)[preE7PairAction 16 p ⧸ N.1] X) X := by
  have hsplit :=
    Q.omegaSocle_schurSocleMultiplicity_le_projectionKernel_add_inner R N X
  have houter :=
    Q.outerOmega_nonfixed_schurSocleMultiplicity_le_two_mul_end_finrank
      R N X hnonfixed
  have hinner :=
    Q.innerOmega_nonfixed_schurSocleMultiplicity_le_end_finrank
      R N X hnonfixed
  exact hsplit.trans (by omega)

/-- A finite nested-quotient generator declaration and a finite coupled
registry close the complete omega-socle cap-four theorem for any paired
tower realization. -/
theorem omegaSocle_schurCapacity_le_four
    (C : DegreeTwoPairTopCoupledRegistryData D 4)
    (R : DegreeTwoPairTopTowerRealization D p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal}) :
    representationSchurCapacity (Q.omegaSocleRepresentation R N) ≤ 4 := by
  apply representationSchurCapacity_le_of_fixed_nonfixed_multiplicity
    (Q.omegaSocleRepresentation R N) 4
  · exact (Q.omegaSocle_invariants_finrank_eq_rawOmega R N).trans_le
      (C.rawKernelOmega_invariants_finrank_le R N)
  · intro X _hX hnonfixed
    have hthree :=
      Q.omegaSocle_nonfixed_schurSocleMultiplicity_le_three_mul_end_finrank
        R N X hnonfixed
    exact hthree.trans (by omega)

end DegreeTwoPairTopNestedQuotientGeneratorData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
