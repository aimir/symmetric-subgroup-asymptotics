import SymmetricSubgroupAsymptotics.CFSGE6GenerationExtractionPilot
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckAdjacentPair
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalCollecting

/-! The first two actual root-line recoveries from the selected E6
pair. Weyl conjugation identities, not degree labels, identify every
parameter. This still stops short of whole-group two-generation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGE6GenerationFirstRootRecovery
open CFSGE6GenerationTorusPilot CFSGE6GenerationExtractionPilot
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGSerreQuadraticMatrix CFSGNormTwoRootPairing
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

abbrev W (K : Type) [Field K] (i : Fin 6) : Ambient K := canonicalWeyl e6Data K i

theorem orthogonal_commute (K : Type) [Field K] (i j : Fin 6)
    (hij : CartanMatrix.E₆ i j=0) (a : K) : Commute (W K i) (root K j a) := by
  have hh := CFSGNormTwoGeckOrthogonalCollecting.orthogonal_word CartanMatrix.E₆
    CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K i j
    (by rw [E6_cartan]; exact hij) a
  exact mul_inv_eq_iff_eq_mul.mp hh

theorem adjacent_pair (K : Type) [Field K] (i j : Fin 6)
    (hij : CartanMatrix.E₆ i j= -1) (hji : CartanMatrix.E₆ j i= -1) (a : K) :
    (W K i*W K j)*root K i a*(W K i*W K j)⁻¹=root K j a :=
  CFSGNormTwoGeckAdjacentPair.adjacent_pair_word CartanMatrix.E₆
    CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K i j
    (by rw [E6_cartan]; exact hij) (by rw [E6_cartan]; exact hji) a

theorem coxeter_sends_four_to_five (K : Type) [Field K] (a : K) :
    coxeter K*root K 4 a*(coxeter K)⁻¹=root K 5 a := by
  let p : Ambient K := W K 0*W K 1*W K 2*W K 3
  have hp : Commute p (root K 5 a) :=
    (((orthogonal_commute K 0 5 (by decide) a).mul_left
      (orthogonal_commute K 1 5 (by decide) a)).mul_left
      (orthogonal_commute K 2 5 (by decide) a)).mul_left
      (orthogonal_commute K 3 5 (by decide) a)
  have hc : coxeter K=p*(W K 4*W K 5) := by
    dsimp only [coxeter,CFSGE6GenerationLatticePilot.coxeterWord,
      CFSGNormTwoGeckWeylWordDegree.wordUnit,p,W]
    group
  rw [hc]
  calc
    _=p*((W K 4*W K 5)*root K 4 a*(W K 4*W K 5)⁻¹)*p⁻¹ := by group
    _=p*root K 5 a*p⁻¹ := by rw [adjacent_pair K 4 5 (by decide) (by decide)]
    _=root K 5 a := hp.mul_inv_cancel

theorem coxeter_sends_three_to_four (K : Type) [Field K] (a : K) :
    coxeter K*root K 3 a*(coxeter K)⁻¹=root K 4 a := by
  let p : Ambient K := W K 0*W K 1*W K 2
  have hp : Commute p (root K 4 a) :=
    ((orthogonal_commute K 0 4 (by decide) a).mul_left
      (orthogonal_commute K 1 4 (by decide) a)).mul_left
      (orthogonal_commute K 2 4 (by decide) a)
  have hs := orthogonal_commute K 5 3 (by decide) a
  have hc : coxeter K=p*(W K 3*W K 4)*W K 5 := by
    dsimp only [coxeter,CFSGE6GenerationLatticePilot.coxeterWord,
      CFSGNormTwoGeckWeylWordDegree.wordUnit,p,W]
    group
  rw [hc]
  calc
    _=p*((W K 3*W K 4)*(W K 5*root K 3 a*(W K 5)⁻¹)*
      (W K 3*W K 4)⁻¹)*p⁻¹ := by group
    _=p*((W K 3*W K 4)*root K 3 a*(W K 3*W K 4)⁻¹)*p⁻¹ := by rw [hs.mul_inv_cancel]
    _=p*root K 4 a*p⁻¹ := by rw [adjacent_pair K 3 4 (by decide) (by decide)]
    _=root K 4 a := hp.mul_inv_cancel

theorem coxeter_inverse_five (K : Type) [Field K] (a : K) :
    (coxeter K)⁻¹*root K 5 a*coxeter K=root K 4 a := by
  have hh := congrArg (fun x : Ambient K=>(coxeter K)⁻¹*x*coxeter K)
    (coxeter_sends_four_to_five K a)
  simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hh.symm

theorem coxeter_inverse_four (K : Type) [Field K] (a : K) :
    (coxeter K)⁻¹*root K 4 a*coxeter K=root K 3 a := by
  have hh := congrArg (fun x : Ambient K=>(coxeter K)⁻¹*x*coxeter K)
    (coxeter_sends_three_to_four K a)
  simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hh.symm

theorem cleaned_inverse_five (K : Type) [Field K] (a : K) :
    (cleanedGenerator K)⁻¹*root K 5 a*cleanedGenerator K=root K 4 a := by
  change (root K 0 1*coxeter K)⁻¹*root K 5 a*(root K 0 1*coxeter K)=_
  calc
    _=(coxeter K)⁻¹*((root K 0 1)⁻¹*root K 5 a*root K 0 1)*coxeter K := by group
    _=(coxeter K)⁻¹*root K 5 a*coxeter K := by rw [(zero_five_commute K 1 a).inv_mul_cancel]
    _=root K 4 a := coxeter_inverse_five K a

theorem cleaned_inverse_four (K : Type) [Field K] (a : K) :
    (cleanedGenerator K)⁻¹*root K 4 a*cleanedGenerator K=root K 3 a := by
  have hh : Commute (root K 0 1) (root K 4 a) := by
    apply CFSGSerreQuadraticCommutingRoots.roots_commute
    exact CFSGNormTwoGeckRationalAdjointStrings.lie_of_cartan_zero CartanMatrix.E₆
      CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index 0 4
      (by rw [E6_cartan]; decide)
  change (root K 0 1*coxeter K)⁻¹*root K 4 a*(root K 0 1*coxeter K)=_
  calc
    _=(coxeter K)⁻¹*((root K 0 1)⁻¹*root K 4 a*root K 0 1)*coxeter K := by group
    _=(coxeter K)⁻¹*root K 4 a*coxeter K := by rw [hh.inv_mul_cancel]
    _=root K 3 a := coxeter_inverse_four K a

theorem pair_recovers_three_four_five (K : Type) [Field K] [Finite K]
    (hcard : 3≤Nat.card K) (g : Kˣ) (hg : ∀u : Kˣ,u∈Subgroup.zpowers g) :
    ∀a : K,root K 3 a∈pairGroup K g ∧ root K 4 a∈pairGroup K g ∧
      root K 5 a∈pairGroup K g := by
  obtain ⟨hfive,hz⟩ := pair_recovers_fifth_line K hcard g hg
  have hfour (a : K) : root K 4 a∈pairGroup K g := by
    rw [←cleaned_inverse_five]
    exact (pairGroup K g).mul_mem ((pairGroup K g).mul_mem
      ((pairGroup K g).inv_mem hz) (hfive a)) hz
  intro a
  refine ⟨?_,hfour a,hfive a⟩
  rw [←cleaned_inverse_four]
  exact (pairGroup K g).mul_mem ((pairGroup K g).mul_mem
    ((pairGroup K g).inv_mem hz) (hfour a)) hz

end SymmetricSubgroupAsymptotics.CFSGE6GenerationFirstRootRecovery
