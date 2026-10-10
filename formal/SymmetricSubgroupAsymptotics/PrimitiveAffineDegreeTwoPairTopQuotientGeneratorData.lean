import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopTowerCoupledHeads
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

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

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

/-- The finite generator declaration gives the uniform nonfixed bound after
pullback along any surjective action map. -/
theorem subrepresentationQuotient_comp_nonfixed_le_end_finrank
    {H X : Type*} [Group H]
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
        (A := ((nestedQuotientRepresentation A B hAB).comp gamma).asModule)
        (X := S) ≤
      Module.finrank (Module.End (ZMod 2)[H] S) S := by
  letI : FiniteDimensional (ZMod 2) X :=
    Module.Finite.of_finite (ZMod 2) X
  letI : FiniteDimensional (ZMod 2) S :=
    Module.Finite.of_finite (ZMod 2) S
  rcases Q.certificate A B hAB with hgen | hsmall
  · let tau := nestedQuotientRepresentation A B hAB
    have hgenComp : RepresentationGeneratedBy (tau.dual.comp gamma) 1 :=
      RepresentationGeneratedBy.comp_of_surjective
        tau.dual gamma hgamma hgen
    let E := representationDualCompEquiv tau gamma
    have hdual : RepresentationGeneratedBy (tau.comp gamma).dual 1 :=
      representationGeneratedBy_of_surjective
        (tau.dual.comp gamma) (tau.comp gamma).dual
        E.symm.toIntertwiningMap E.symm.surjective hgenComp
    have hschur := schurSocleMultiplicity_le_of_dual_generated
      (tau.comp gamma) 1 hdual (X := S)
    simpa only [tau, one_mul] using hschur
  · have hone : schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[H])
        (A := ((nestedQuotientRepresentation A B hAB).comp gamma).asModule)
        (X := S) ≤ 1 :=
      schurSocleMultiplicity_le_one_of_finrank_le_two_of_nonfixed
        sigma S hnonfixed hsmall
    have hpos : 0 < Module.finrank (Module.End (ZMod 2)[H] S) S := by
      letI : Nontrivial S := IsSimpleModule.nontrivial (ZMod 2)[H] S
      exact Module.finrank_pos
        (R := Module.End (ZMod 2)[H] S) (M := S)
    exact hone.trans hpos

/-! ## Physical two-frame consequences -/

variable {p : PreE7PairActionClass 16}

/-- Canonical socle of the direct-kernel omega representation. -/
abbrev omegaSocleRepresentation
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
    (X : Submodule (ZMod 2)[preE7PairAction 16 p ⨸ N.1]
      (Q.omegaSocleRepresentation R N).asModule)
    [IsSimpleModule (ZMod 2)[preE7PairAction 16 p ⨸ N.1] X] :
    schurSocleMultiplicity
        (k := ZMod 2)
        (R := (ZMod 2)[preE7PairAction 16 p ⨸ N.1])
        (A := (Q.omegaSocleRepresentation R N).asModule) (X := X) =
      schurSocleMultiplicity
        (k := ZMod 2)
        (R := (ZMod 2)[preE7PairAction 16 p ⨸ N.1])
        (A := (binaryKernelOmegaConjugationRepresentation
          (R.rawQuotientMap N)).asModule) (X := X) :=
  finiteRepresentationSocle_schurSocleMultiplicity_eq
    (binaryKernelOmegaConjugationRepresentation (R.rawQuotientMap N))

theorem omegaSocle_schurSocleMultiplicity_le_projectionKernel_add_inner
    (R : DegreeTwoPairTopTowerRealization D p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal})
    (X : Submodule (ZMod 2)[preE7PairAction 16 p ⨸ N.1]
      (Q.omegaSocleRepresentation R N).asModule)
    [IsSimpleModule (ZMod 2)[preE7PairAction 16 p ⨸ N.1] X] :
    schurSocleMultiplicity
        (k := ZMod 2)
        (R := (ZMod 2)[preE7PairAction 16 p ⨸ N.1])
        (A := (Q.omegaSocleRepresentation R N).asModule) (X := X) ≤
      schurSocleMultiplicity
          (k := ZMod 2)
          (R := (ZMod 2)[preE7PairAction 16 p ⨸ N.1])
          (A := (R.rawKernelOmegaInnerImageIntertwiner N).ker.asSubmodule)
          (X := X) +
        schurSocleMultiplicity
          (k := ZMod 2)
          (R := (ZMod 2)[preE7PairAction 16 p ⨸ N.1])
          (A := ((R.innerOmegaSubrepresentation N).toRepresentation.comp
            (R.rawQuotientMap N)).asModule) (X := X) := by
  rw [Q.omegaSocle_schurSocleMultiplicity_eq_rawOmega R N X]
  exact representationSchurMultiplicity_le_kernel_add_target
    (binaryKernelOmegaConjugationRepresentation (R.rawQuotientMap N))
    ((R.innerOmegaSubrepresentation N).toRepresentation.comp
      (R.rawQuotientMap N))
    (R.rawKernelOmegaInnerImageIntertwiner N)
    (R.rawKernelOmegaInnerImageIntertwiner_surjective N)

/-- The two fixed first-frame endpoints each cost one nonfixed Schur
dimension after arbitrary inflation. -/
theorem outerNestedQuotient_comp_nonfixed_le_two_mul
    (R : DegreeTwoPairTopTowerRealization D p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal})
    {H A : Type*} [Group H]
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

/-- The actual inner projection image costs one nonfixed Schur dimension. -/
theorem innerOmega_nonfixed_schurSocleMultiplicity_le_end_finrank
    (R : DegreeTwoPairTopTowerRealization D p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal})
    (X : Submodule (ZMod 2)[preE7PairAction 16 p ⨸ N.1]
      (Q.omegaSocleRepresentation R N).asModule)
    [IsSimpleModule (ZMod 2)[preE7PairAction 16 p ⨸ N.1] X]
    (hnonfixed : ¬ representationSubmoduleFixed
      (Q.omegaSocleRepresentation R N) X) :
    schurSocleMultiplicity
        (k := ZMod 2)
        (R := (ZMod 2)[preE7PairAction 16 p ⨸ N.1])
        (A := ((R.innerOmegaSubrepresentation N).toRepresentation.comp
          (R.rawQuotientMap N)).asModule) (X := X) ≤
      Module.finrank
        (Module.End (ZMod 2)[preE7PairAction 16 p ⨸ N.1] X) X := by
  let A := R.moduleAxis N
  let B := R.innerOmegaNaturalAxis N
  let hAB := R.moduleAxis_le_innerOmegaNaturalAxis N
  let tau := nestedQuotientRepresentation A B hAB
  let sigma := (R.innerOmegaSubrepresentation N).toRepresentation
  let q := QuotientGroup.mk' (R.topNormal N.1)
  let E : tau.Equiv (sigma.comp q) :=
    R.innerNestedQuotientEquivInnerOmegaInflation N
  letI : FiniteDimensional (ZMod 2) X :=
    Module.Finite.of_finite (ZMod 2) X
  rcases Q.certificate A B hAB with hgen | hsmall
  · have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
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
  · have htarget : Module.finrank (ZMod 2)
        ((sigma.comp (R.rawQuotientMap N)).asModule) ≤ 2 := by
      have hE := E.toLinearEquiv.finrank_eq
      have hsigma : Module.finrank (ZMod 2) sigma.asModule ≤ 2 := by
        rw [← hE]
        exact hsmall
      simpa only [sigma] using hsigma
    exact schurSocleMultiplicity_le_one_of_finrank_le_two_of_nonfixed
      (Q.omegaSocleRepresentation R N) X hnonfixed htarget

/-- The physical outer projection kernel costs two nonfixed Schur
dimensions. -/
theorem outerOmega_nonfixed_schurSocleMultiplicity_le_two_mul_end_finrank
    (R : DegreeTwoPairTopTowerRealization D p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal})
    (X : Submodule (ZMod 2)[preE7PairAction 16 p ⨸ N.1]
      (Q.omegaSocleRepresentation R N).asModule)
    [IsSimpleModule (ZMod 2)[preE7PairAction 16 p ⨸ N.1] X]
    (hnonfixed : ¬ representationSubmoduleFixed
      (Q.omegaSocleRepresentation R N) X) :
    schurSocleMultiplicity
        (k := ZMod 2)
        (R := (ZMod 2)[preE7PairAction 16 p ⨸ N.1])
        (A := (R.rawKernelOmegaInnerImageIntertwiner N).ker.asSubmodule)
        (X := X) ≤
      2 * Module.finrank
        (Module.End (ZMod 2)[preE7PairAction 16 p ⨸ N.1] X) X := by
  let GQ := preE7PairAction 16 p ⨸ N.1
  let G := preE7PairAction 16 p
  let gamma : G →* GQ := QuotientGroup.mk' N.1
  have hgamma : Function.Surjective gamma := QuotientGroup.mk'_surjective _
  let omega := Q.omegaSocleRepresentation R N
  let outer := (R.rawKernelOmegaInnerImageIntertwiner N).ker.toRepresentation
  let rhoX := (Subrepresentation.ofSubmodule' X).toRepresentation
  let sigmaG := omega.comp gamma
  let XG := representationInflatedSubmodule gamma hgamma omega X
  letI : FiniteDimensional (ZMod 2) X :=
    Module.Finite.of_finite (ZMod 2) X
  letI : IsSimpleModule (ZMod 2)[GQ] rhoX.asModule := by
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
        (k := ZMod 2) (R := (ZMod 2)[GQ])
        (A := outer.asModule) (X := rhoX.asModule) =
      schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[GQ])
        (A := outer.asModule) (X := X) :=
    schurSocleMultiplicity_eq_of_source_linearEquiv
      (submoduleRepresentationModuleEquiv omega X)
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
        (R.rawKernelOmegaInnerImageIntertwiner N).ker.asSubmodule)
  have hendG := moduleFinrankOverEnd_eq_of_linearEquiv eXmodule
  have hendInflate := representationFinrankOverEnd_comp_eq
    gamma hgamma rhoX
  have hendQ := moduleFinrankOverEnd_eq_of_linearEquiv
    (submoduleRepresentationModuleEquiv omega X)
  have hend : Module.finrank (Module.End (ZMod 2)[G] XG) XG =
      Module.finrank (Module.End (ZMod 2)[GQ] X) X :=
    hendG.symm.trans (hendInflate.trans hendQ)
  rw [← hsourceG, hinflate, hsourceQ, htargetQ, hend] at hphysicalG
  simpa only [outer, GQ] using hphysicalG

/-- The inner and outer pair sections give the uniform coefficient-three
bound for every nonfixed simple row. -/
theorem omegaSocle_nonfixed_schurSocleMultiplicity_le_three_mul_end_finrank
    (R : DegreeTwoPairTopTowerRealization D p)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal})
    (X : Submodule (ZMod 2)[preE7PairAction 16 p ⨸ N.1]
      (Q.omegaSocleRepresentation R N).asModule)
    [IsSimpleModule (ZMod 2)[preE7PairAction 16 p ⨸ N.1] X]
    (hnonfixed : ¬ representationSubmoduleFixed
      (Q.omegaSocleRepresentation R N) X) :
    schurSocleMultiplicity
        (k := ZMod 2)
        (R := (ZMod 2)[preE7PairAction 16 p ⨸ N.1])
        (A := (Q.omegaSocleRepresentation R N).asModule) (X := X) ≤
      3 * Module.finrank
        (Module.End (ZMod 2)[preE7PairAction 16 p ⨸ N.1] X) X := by
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
  · rw [Q.omegaSocle_invariants_finrank_eq_rawOmega R N]
    exact C.rawKernelOmega_invariants_finrank_le R N
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
