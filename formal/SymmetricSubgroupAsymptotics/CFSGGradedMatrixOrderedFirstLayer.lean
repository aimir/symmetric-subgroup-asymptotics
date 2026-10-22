import SymmetricSubgroupAsymptotics.CFSGGradedMatrixGroupFirstLayer
import Mathlib.Algebra.BigOperators.Fin

/-! Ordered positive matrix products have the sum of their actual leading
coefficients. Removing an ordered product with the same first layer leaves
a genuine height-at-least-two remainder, without logarithms. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGradedMatrixOrderedFirstLayer
open CFSGGradedMatrixLieFirstLayer CFSGGradedMatrixGroupFirstLayer CFSGGradedMatrixSubgroups
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

theorem list_product_firstLayer (weight : I→ℤ) (l : List (Matrix I I K)ˣ)
    (hl : ∀u∈l,u∈strictUnits weight) :
    l.prod∈strictUnits weight ∧
      firstLayer weight l.prod=(l.map (firstLayer weight)).sum := by
  revert hl
  induction l with
  | nil=>
    intro hl
    refine ⟨(strictUnits weight).one_mem,?_⟩
    simp only [List.prod_nil,firstLayer_one,List.map_nil,List.sum_nil]
  | cons u l ih=>
    intro hl
    have hu := hl u (by simp)
    have htail : ∀v∈l,v∈strictUnits weight := fun v hv=>hl v (by simp [hv])
    obtain ⟨hp,hfirst⟩ := ih htail
    refine ⟨(strictUnits weight).mul_mem hu hp,?_⟩
    rw [List.prod_cons,firstLayer_mul weight u l.prod hu hp,hfirst,List.map_cons,List.sum_cons]

theorem matching_firstLayer_correction (weight : I→ℤ) (u v : (Matrix I I K)ˣ)
    (hu : u∈strictUnits weight) (hv : v∈strictUnits weight)
    (hfirst : firstLayer weight u=firstLayer weight v) :
    firstLayer weight (u*v⁻¹)=0 := by
  rw [firstLayer_mul weight u v⁻¹ hu ((strictUnits weight).inv_mem hv),
    firstLayer_inv weight v hv,hfirst,add_neg_cancel]

theorem height_two_of_firstLayer_zero (weight : I→ℤ) (u : (Matrix I I K)ˣ)
    (hu : u∈strictUnits weight) (hfirst : firstLayer weight u=0) :
    ∀i j,weight i≤weight j+1→(u : Matrix I I K) i j=(1 : Matrix I I K) i j := by
  intro i j hij
  by_cases hlow : weight i≤weight j
  · exact hu i j hlow
  · have heq : weight i=weight j+1 := by omega
    have hh := congrArg (fun M : Matrix I I K=>M i j) hfirst
    change (if weight i=weight j+1 then
      (u : Matrix I I K) i j-(1 : Matrix I I K) i j else 0)=0 at hh
    rw [if_pos heq] at hh
    exact sub_eq_zero.mp hh

end SymmetricSubgroupAsymptotics.CFSGGradedMatrixOrderedFirstLayer
