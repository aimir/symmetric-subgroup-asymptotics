import SymmetricSubgroupAsymptotics.CFSGGradedMatrixGroupSecondLayer
import Mathlib.Algebra.BigOperators.Fin

/-! Actual ordered products in the second height layer. A matching
product leaves a height-at-least-three remainder, in any characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGradedMatrixOrderedSecondLayer
open CFSGGradedMatrixGroupFirstLayer CFSGGradedMatrixGroupSecondLayer
open CFSGGradedMatrixSubgroups CFSGGradedMatrixOrderedFirstLayer
open CFSGGradedMatrixSingleDegreeSpan
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

theorem list_product_secondLayer (weight : I→ℤ) (l : List (Matrix I I K)ˣ)
    (hl : ∀u∈l,u∈strictUnits weight ∧ firstLayer weight u=0) :
    l.prod∈strictUnits weight ∧ firstLayer weight l.prod=0 ∧
      secondLayer weight l.prod=(l.map (secondLayer weight)).sum := by
  revert hl
  induction l with
  | nil=>
    intro hl
    refine ⟨(strictUnits weight).one_mem,firstLayer_one weight,?_⟩
    simp only [List.prod_nil,secondLayer_one,List.map_nil,List.sum_nil]
  | cons u l ih=>
    intro hl
    obtain ⟨hu,hu0⟩ := hl u (by simp)
    have htail : ∀v∈l,v∈strictUnits weight ∧ firstLayer weight v=0 :=
      fun v hv=>hl v (by simp [hv])
    obtain ⟨hp,hp0,hsecond⟩ := ih htail
    refine ⟨(strictUnits weight).mul_mem hu hp,?_,?_⟩
    · rw [List.prod_cons,firstLayer_mul weight u l.prod hu hp,hu0,hp0,add_zero]
    · rw [List.prod_cons,secondLayer_mul weight u l.prod hu hp hu0,hsecond,
        List.map_cons,List.sum_cons]

theorem matching_secondLayer_correction (weight : I→ℤ) (u v : (Matrix I I K)ˣ)
    (hu : u∈strictUnits weight) (hv : v∈strictUnits weight)
    (hu0 : firstLayer weight u=0)
    (hv0 : firstLayer weight v=0)
    (hsecond : secondLayer weight u=secondLayer weight v) :
    secondLayer weight (u*v⁻¹)=0 := by
  rw [secondLayer_mul weight u v⁻¹ hu ((strictUnits weight).inv_mem hv) hu0,
    secondLayer_inv weight v hv hv0,hsecond,add_neg_cancel]

theorem height_three_of_secondLayer_zero (weight : I→ℤ) (u : (Matrix I I K)ˣ)
    (hu : u∈strictUnits weight) (hu0 : firstLayer weight u=0)
    (hsecond : secondLayer weight u=0) :
    ∀i j,weight i≤weight j+2→
      (u : Matrix I I K) i j=(1 : Matrix I I K) i j := by
  intro i j hij
  by_cases hlow : weight i≤weight j+1
  · exact height_two_of_firstLayer_zero weight u hu hu0 i j hlow
  · have heq : weight i=weight j+2 := by omega
    have hh := congrArg (fun M : Matrix I I K=>M i j) hsecond
    change (if weight i=weight j+2 then
      (u : Matrix I I K) i j-(1 : Matrix I I K) i j else 0)=0 at hh
    rw [if_pos heq] at hh
    exact sub_eq_zero.mp hh

end SymmetricSubgroupAsymptotics.CFSGGradedMatrixOrderedSecondLayer
