import SymmetricSubgroupAsymptotics.CFSGE6GenerationFirstRootRecovery
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalWeyl

/-! The same selected E6 word transports the original node0 line to
node2 and recovers an actual conjugate of node3. The latter is defined
by its literal matrix word, not identified from a lattice degree. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGE6GenerationBranchRoot
open CFSGE6GenerationTorusPilot CFSGE6GenerationExtractionPilot
open CFSGE6GenerationFirstRootRecovery CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoRootPairing
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

theorem coxeter_sends_zero_to_two (K : Type) [Field K] (a : K) :
    coxeter K*root K 0 a*(coxeter K)⁻¹=root K 2 a := by
  let s : Ambient K := W K 1*W K 3*W K 4*W K 5
  have hs : Commute s (root K 0 a) :=
    (((orthogonal_commute K 1 0 (by decide) a).mul_left
      (orthogonal_commute K 3 0 (by decide) a)).mul_left
      (orthogonal_commute K 4 0 (by decide) a)).mul_left
      (orthogonal_commute K 5 0 (by decide) a)
  have h12 : W K 1*W K 2=W K 2*W K 1 :=
    (CFSGNormTwoGeckOrthogonalWeyl.orthogonal_weyls CartanMatrix.E₆
      CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K 1 2
      (by rw [E6_cartan]; decide)).eq
  have hc : coxeter K=(W K 0*W K 2)*s := by
    calc
      _=W K 0*(W K 1*W K 2)*(W K 3*W K 4*W K 5) := by
        dsimp only [coxeter,CFSGE6GenerationLatticePilot.coxeterWord,
          CFSGNormTwoGeckWeylWordDegree.wordUnit,W]
        group
      _=W K 0*(W K 2*W K 1)*(W K 3*W K 4*W K 5) := by rw [h12]
      _=(W K 0*W K 2)*s := by dsimp only [s]; group
  rw [hc]
  calc
    _=(W K 0*W K 2)*(s*root K 0 a*s⁻¹)*(W K 0*W K 2)⁻¹ := by group
    _=(W K 0*W K 2)*root K 0 a*(W K 0*W K 2)⁻¹ := by rw [hs.mul_inv_cancel]
    _=root K 2 a := adjacent_pair K 0 2 (by decide) (by decide) a

def branchRoot (K : Type) [Field K] (a : K) : Ambient K :=
  (coxeter K)⁻¹*root K 3 a*coxeter K

theorem cleaned_inverse_three (K : Type) [Field K] (a : K) :
    (cleanedGenerator K)⁻¹*root K 3 a*cleanedGenerator K=branchRoot K a := by
  have hh : Commute (root K 0 1) (root K 3 a) :=
    CFSGNormTwoGeckOrthogonalWeyl.orthogonal_signed_roots CartanMatrix.E₆
      CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K 0 3
      (by rw [E6_cartan]; decide) false false 1 a
  change (root K 0 1*coxeter K)⁻¹*root K 3 a*(root K 0 1*coxeter K)=_
  calc
    _=(coxeter K)⁻¹*((root K 0 1)⁻¹*root K 3 a*root K 0 1)*coxeter K := by group
    _=(coxeter K)⁻¹*root K 3 a*coxeter K := by rw [hh.inv_mul_cancel]

theorem pair_recovers_branch_line (K : Type) [Field K] [Finite K]
    (hcard : 3≤Nat.card K) (g : Kˣ) (hg : ∀u : Kˣ,u∈Subgroup.zpowers g) :
    ∀a : K,branchRoot K a∈pairGroup K g := by
  have hz := (pair_recovers_fifth_line K hcard g hg).2
  intro a
  rw [←cleaned_inverse_three]
  exact (pairGroup K g).mul_mem ((pairGroup K g).mul_mem
    ((pairGroup K g).inv_mem hz) ((pair_recovers_three_four_five K hcard g hg a).1)) hz

end SymmetricSubgroupAsymptotics.CFSGE6GenerationBranchRoot
