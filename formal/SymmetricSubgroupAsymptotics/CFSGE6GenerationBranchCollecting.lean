import SymmetricSubgroupAsymptotics.CFSGE6GenerationBranchRoot
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterizedCollecting
import SymmetricSubgroupAsymptotics.CFSGAdditiveConjugationFactorsCommute

/-! Exact A2 collecting for the actual conjugate branch root. Every
family retains its original matrix word, rather than a root-degree label. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGE6GenerationBranchCollecting
open CFSGE6GenerationTorusPilot CFSGE6GenerationBranchRoot
open CFSGE6GenerationFirstRootRecovery CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoRootPairing
open CFSGSerreQuadraticMatrix
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

def mixedRoot (K : Type) [Field K] (a : K) : Ambient K :=
  (coxeter K)⁻¹*(W K 2*root K 3 a*(W K 2)⁻¹)*coxeter K

theorem zero_eq_inverse_conjugate_two (K : Type) [Field K] (a : K) :
    root K 0 a=(coxeter K)⁻¹*root K 2 a*coxeter K := by
  have hh := congrArg (fun x : Ambient K=>(coxeter K)⁻¹*x*coxeter K)
    (coxeter_sends_zero_to_two K a)
  simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hh

theorem zero_branch_conjugation (K : Type) [Field K] (t a : K) :
    root K 0 t*branchRoot K a*(root K 0 t)⁻¹=mixedRoot K (a*t)*branchRoot K a := by
  simp only [zero_eq_inverse_conjugate_two]
  dsimp only [branchRoot,mixedRoot]
  calc
    _=(coxeter K)⁻¹*(root K 2 t*root K 3 a*(root K 2 t)⁻¹)*coxeter K := by group
    _=(coxeter K)⁻¹*((W K 2*root K 3 (a*t)*(W K 2)⁻¹)*root K 3 a)*coxeter K := by
      dsimp only [root,W]
      rw [CFSGNormTwoGeckParameterizedCollecting.adjacent_conjugation_factor
        CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K 2 3
        (by rw [E6_cartan]; decide)]
    _=_ := by group

theorem branchRoot_add (K : Type) [Field K] (a b : K) :
    branchRoot K (a+b)=branchRoot K a*branchRoot K b := by
  dsimp only [branchRoot,root]
  rw [←canonicalRoot_add]
  group

theorem mixedRoot_add (K : Type) [Field K] (a b : K) :
    mixedRoot K (a+b)=mixedRoot K a*mixedRoot K b := by
  dsimp only [mixedRoot,root]
  rw [←canonicalRoot_add]
  group

theorem branch_mixed_commute (K : Type) [Field K] (a b : K) :
    Commute (branchRoot K a) (mixedRoot K b) := by
  apply CFSGAdditiveConjugationFactorsCommute.factors_commute
    (root K 0 1) (branchRoot K) (mixedRoot K)
    (branchRoot_add K) (mixedRoot_add K)
  intro c
  simpa only [mul_one] using zero_branch_conjugation K 1 c

end SymmetricSubgroupAsymptotics.CFSGE6GenerationBranchCollecting
