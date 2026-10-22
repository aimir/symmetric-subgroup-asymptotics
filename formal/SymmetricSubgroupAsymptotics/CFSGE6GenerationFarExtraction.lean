import SymmetricSubgroupAsymptotics.CFSGE6GenerationFarFactors
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckConjugateCharacter
import SymmetricSubgroupAsymptotics.CFSGFixedFactorScalarExtraction

/-! Actual extraction of the far mixed root WORD from the same two
E6 generators over every finite field of cardinality at least3. Its
identification with an original negative simple-root line remains a
separate matrix identity, not an inference from a degree label. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGE6GenerationFarExtraction
open CFSGE6GenerationTorusPilot CFSGE6GenerationExtractionPilot
open CFSGE6GenerationFarFactors CFSGE6GenerationBranchLattice
open CFSGE6GenerationLatticePilot CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoRootPairing
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckCharacterDiagonal
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

theorem torus_fixes_far_branch (K : Type) [Field K] (g : Kˣ) (a : K) :
    torus K g*farBranch K a*(torus K g)⁻¹=farBranch K a := by
  simp only [far_branch_as_word]
  have hh := CFSGNormTwoGeckConjugateCharacter.conjugate_root_scaling
    CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K
    torusFunctional g farBranchWord 3 a
  change torus K g*
    (wordUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K farBranchWord*
      root K 3 a*
      (wordUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K farBranchWord)⁻¹)*
    (torus K g)⁻¹=
      wordUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K farBranchWord*
      root K 3 (a*(g:K)^(torusFunctional
        (wordLinear CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index farBranchWord
          (Pi.single 3 1))))*
      (wordUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K farBranchWord)⁻¹ at hh
  simpa only [far_branch_character,zpow_zero,mul_one] using hh

theorem torus_scales_far_mixed (K : Type) [Field K] (g : Kˣ) (a : K) :
    torus K g*farMixed K a*(torus K g)⁻¹=farMixed K ((g:K)⁻¹*a) := by
  simp only [far_mixed_as_word]
  have hh := CFSGNormTwoGeckConjugateCharacter.conjugate_root_scaling
    CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K
    torusFunctional g farMixedWord 3 a
  change torus K g*
    (wordUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K farMixedWord*
      root K 3 a*
      (wordUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K farMixedWord)⁻¹)*
    (torus K g)⁻¹=
      wordUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K farMixedWord*
      root K 3 (a*(g:K)^(torusFunctional
        (wordLinear CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index farMixedWord
          (Pi.single 3 1))))*
      (wordUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K farMixedWord)⁻¹ at hh
  simpa only [far_mixed_character,zpow_neg_one,mul_comm] using hh

theorem pair_recovers_far_mixed (K : Type) [Field K] [Finite K]
    (hcard : 3≤Nat.card K) (g : Kˣ) (hg : ∀u : Kˣ,u∈Subgroup.zpowers g) :
    ∀a : K,farMixed K a∈pairGroup K g := by
  have hk : (g:K)⁻¹≠1 := by
    intro h
    apply CFSGOrthogonalDGenerationScalarFilter.primitive_ne_one hcard g hg
    have hh := congrArg (fun x : K=>x⁻¹) h
    simpa only [inv_inv,inv_one] using hh
  apply CFSGFixedFactorScalarExtraction.all_scaled_parameters
    (farBranch K) (farMixed K) (farMixed_add K) (farMixed_zero K)
    (torus K g) (g:K)⁻¹ hk (torus_fixes_far_branch K g) (torus_scales_far_mixed K g)
    (pairGroup K g)
  · exact Subgroup.subset_closure (by simp)
  · exact pair_contains_factor K hcard g hg

theorem exists_actual_pair_recovering_far_mixed (K : Type) [Field K] [Finite K]
    (hcard : 3≤Nat.card K) : ∃g : Kˣ,
      pairGroup K g≤CFSGSerreQuadraticMatrix.canonicalElementaryGroup e6Data K ∧
      ∀a : K,farMixed K a∈pairGroup K g := by
  obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α:=Kˣ)
  exact ⟨g,pairGroup_le_canonical K g,pair_recovers_far_mixed K hcard g hg⟩

end SymmetricSubgroupAsymptotics.CFSGE6GenerationFarExtraction
