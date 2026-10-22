import SymmetricSubgroupAsymptotics.CFSGE6GenerationBranchCollecting
import SymmetricSubgroupAsymptotics.CFSGE6GenerationBranchLattice

/-! The next available word splits into two literal conjugate root
families. Both are retained as actual matrix words; the lattice pilot
will supply their different character weights. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGE6GenerationFarFactors
open CFSGE6GenerationTorusPilot CFSGE6GenerationExtractionPilot
open CFSGE6GenerationBranchRoot CFSGE6GenerationBranchCollecting
open CFSGE6GenerationFirstRootRecovery CFSGE6GenerationBranchLattice
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

def farBranch (K : Type) [Field K] (a : K) : Ambient K :=
  (coxeter K)⁻¹*branchRoot K a*coxeter K

def farMixed (K : Type) [Field K] (a : K) : Ambient K :=
  (coxeter K)⁻¹*mixedRoot K a*coxeter K

theorem farMixed_add (K : Type) [Field K] (a b : K) :
    farMixed K (a+b)=farMixed K a*farMixed K b := by
  dsimp only [farMixed]
  rw [mixedRoot_add]
  group

theorem farMixed_zero (K : Type) [Field K] : farMixed K 0=1 := by
  dsimp only [farMixed,mixedRoot,root]
  rw [canonicalRoot_zero]
  group

theorem far_branch_as_word (K : Type) [Field K] (a : K) :
    farBranch K a=
      wordUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K farBranchWord*
        root K 3 a*
      (wordUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K farBranchWord)⁻¹ := by
  simp only [farBranchWord,wordUnit_append,wordUnit_inverseWord]
  dsimp only [farBranch,branchRoot,coxeter]
  group <;> simp only [zpow_two,mul_assoc]

theorem far_mixed_as_word (K : Type) [Field K] (a : K) :
    farMixed K a=
      wordUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K farMixedWord*
        root K 3 a*
      (wordUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K farMixedWord)⁻¹ := by
  have htwo : wordUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base E6Index K [2]=W K 2 := by
    change canonicalWeyl e6Data K 2*1=W K 2
    exact mul_one _
  simp only [farMixedWord,farBranchWord,wordUnit_append,wordUnit_inverseWord,htwo]
  dsimp only [farMixed,mixedRoot,coxeter,W]
  group <;> simp only [zpow_two,mul_assoc]

theorem cleaned_branch_factor (K : Type) [Field K] (a : K) :
    (cleanedGenerator K)⁻¹*branchRoot K a*cleanedGenerator K=
      farMixed K (-a)*farBranch K a := by
  have hi : (root K 0 (-1))⁻¹=root K 0 1 := by
    simpa only [neg_neg] using canonicalRoot_inverse e6Data K false 0 (-1)
  have hh := zero_branch_conjugation K (-1) a
  rw [hi,mul_neg_one] at hh
  have hj : (root K 0 1)⁻¹=root K 0 (-1) := canonicalRoot_inverse e6Data K false 0 1
  change (root K 0 1*coxeter K)⁻¹*branchRoot K a*(root K 0 1*coxeter K)=_
  calc
    _=(coxeter K)⁻¹*((root K 0 1)⁻¹*branchRoot K a*root K 0 1)*coxeter K := by group
    _=(coxeter K)⁻¹*(mixedRoot K (-a)*branchRoot K a)*coxeter K := by rw [hj,hh]
    _=farMixed K (-a)*farBranch K a := by dsimp only [farMixed,farBranch]; group

theorem pair_contains_factor (K : Type) [Field K] [Finite K]
    (hcard : 3≤Nat.card K) (g : Kˣ) (hg : ∀u : Kˣ,u∈Subgroup.zpowers g) (a : K) :
    farMixed K (-a)*farBranch K a∈pairGroup K g := by
  rw [←cleaned_branch_factor]
  have hz := (pair_recovers_fifth_line K hcard g hg).2
  exact (pairGroup K g).mul_mem ((pairGroup K g).mul_mem ((pairGroup K g).inv_mem hz)
    (pair_recovers_branch_line K hcard g hg a)) hz

end SymmetricSubgroupAsymptotics.CFSGE6GenerationFarFactors
