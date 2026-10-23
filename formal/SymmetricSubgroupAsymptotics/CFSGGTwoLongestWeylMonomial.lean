import SymmetricSubgroupAsymptotics.CFSGGTwoWeylMonomial

/-! Exact longest Weyl word in the natural G2 representation. Products
are evaluated through the already checked signed monomial coordinates,
never by expanding a long dense root-word matrix multiplication. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoLongestWeylMonomial
open CFSGGTwoSerreMatrices CFSGGTwoShortWeylMatrices CFSGGTwoWeylMonomial CFSGTypeAMonomialMatrices
open CFSGMonomialProductCoordinates

def cyclePermutation : Equiv.Perm Index := longPermutation*shortPermutation

def oppositePermutation : Equiv.Perm Index := Equiv.sumComm _ _

private theorem cycle_permutation_cube :
    cyclePermutation*(cyclePermutation*cyclePermutation)=oppositePermutation := by
  ext x
  rcases x with i|i <;> fin_cases i <;> decide +kernel

private theorem opposite_permutation_square : oppositePermutation*oppositePermutation=1 := by
  ext x
  cases x <;> rfl

variable (K : Type) [Field K]

def cycleWeight (x : Index) : K := shortWeight K x*longWeight K (shortPermutation x)

private theorem short_weight_condition (x : Index) :
    (shortPermutation x=pos 1 ∨ shortPermutation x=neg 1) ↔
      (x=pos 0 ∨ x=neg 0) := by
  rcases x with i|i <;> fin_cases i <;> decide +kernel

private theorem cycle_weight (x : Index) : cycleWeight K x = -1 := by
  simp only [cycleWeight,shortWeight,longWeight,short_weight_condition]
  split_ifs <;> ring

private theorem cycle_weight_cube (x : Index) :
    (cycleWeight K x*cycleWeight K (cyclePermutation x))*
      cycleWeight K ((cyclePermutation*cyclePermutation) x) = -1 := by
  rw [cycle_weight,cycle_weight,cycle_weight]
  ring

def longestUnit : (Mat K)ˣ := (shortWeyl K*longWeyl K)^3

theorem longestUnit_val :
    (longestUnit K : Mat K)=monomial oppositePermutation (fun _ => (-1:K)) := by
  have hc : (shortWeyl K*longWeyl K : (Mat K)ˣ).val=
      monomial cyclePermutation (cycleWeight K) := by
    simp only [Units.val_mul,shortWeyl_monomial,longWeyl_monomial,monomial_mul]
    rfl
  change ((shortWeyl K*longWeyl K : (Mat K)ˣ).val)^3=_
  rw [pow_succ,pow_succ,pow_one,hc,monomial_mul,monomial_mul,cycle_permutation_cube]
  exact congrArg (fun w : Index → K => monomial oppositePermutation w)
    (funext (cycle_weight_cube K))

theorem longestUnit_square : longestUnit K*longestUnit K=1 := by
  apply Units.ext
  change (longestUnit K : Mat K)*(longestUnit K : Mat K)=(1:Mat K)
  rw [longestUnit_val,monomial_mul,opposite_permutation_square]
  apply Matrix.ext
  intro i j
  by_cases h : j=i
  · subst j
    simp [monomial_apply,Matrix.one_apply]
  · simp [monomial_apply,Matrix.one_apply,h,Ne.symm h]

end SymmetricSubgroupAsymptotics.CFSGGTwoLongestWeylMonomial
