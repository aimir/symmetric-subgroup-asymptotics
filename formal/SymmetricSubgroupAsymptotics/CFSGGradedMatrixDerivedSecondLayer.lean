import SymmetricSubgroupAsymptotics.CFSGGradedMatrixGroupSecondLayer
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixCommutatorSecondLayer
import Mathlib.GroupTheory.Commutator.Basic

/-! The actual derived subgroup has its second height layer in the span
of brackets of genuine first-layer generators. Closure is taken in the
original subgroup, not in an assumed presentation or surrounding Lie algebra. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGradedMatrixDerivedSecondLayer
open CFSGGradedMatrixGroupFirstLayer CFSGGradedMatrixGroupSecondLayer
open CFSGGradedMatrixSubgroups CFSGGradedMatrixCommutatorSecondLayer
variable {I J K : Type*} [Fintype I] [DecidableEq I] [Field K]

def bracketSpan (X : J→Matrix I I K) : Submodule K (Matrix I I K) :=
  Submodule.span K (Set.range (fun p : J×J=>⁅X p.1,X p.2⁆))

theorem bracket_mem_bracketSpan (X : J→Matrix I I K) (M N : Matrix I I K)
    (hM : M∈Submodule.span K (Set.range X))
    (hN : N∈Submodule.span K (Set.range X)) : ⁅M,N⁆∈bracketSpan X := by
  revert N hN
  induction hM using Submodule.span_induction with
  | mem M hM=>
    obtain ⟨i,rfl⟩ := hM
    intro N hN
    induction hN using Submodule.span_induction with
    | mem N hN=>
      obtain ⟨j,rfl⟩ := hN
      exact Submodule.subset_span ⟨(i,j),rfl⟩
    | zero=>rw [lie_zero];exact Submodule.zero_mem _
    | add N P _ _ hn hp=>rw [lie_add];exact Submodule.add_mem _ hn hp
    | smul a N _ hn=>rw [lie_smul];exact Submodule.smul_mem _ a hn
  | zero=>intro N hN;rw [zero_lie];exact Submodule.zero_mem _
  | add M P _ _ hm hp=>
    intro N hN
    rw [add_lie]
    exact Submodule.add_mem _ (hm N hN) (hp N hN)
  | smul a M _ hm=>
    intro N hN
    rw [smul_lie]
    exact Submodule.smul_mem _ a (hm N hN)

theorem derived_secondLayer_mem_bracketSpan (weight : I→ℤ)
    (P : Subgroup (Matrix I I K)ˣ) (X : J→Matrix I I K)
    (hP : ∀u : P,u.val∈strictUnits weight)
    (hfirst : ∀u : P,firstLayer weight u.val∈Submodule.span K (Set.range X))
    (u : P) (hu : u∈commutator P) :
    firstLayer weight u.val=0 ∧ secondLayer weight u.val∈bracketSpan X := by
  rw [commutator_eq_closure] at hu
  induction hu using Subgroup.closure_induction with
  | mem u hu=>
    obtain ⟨a,b,rfl⟩ := hu
    change firstLayer weight (a.val*b.val*a.val⁻¹*b.val⁻¹)=0 ∧
      secondLayer weight (a.val*b.val*a.val⁻¹*b.val⁻¹)∈bracketSpan X
    refine ⟨commutator_firstLayer_zero weight a.val b.val (hP a) (hP b),?_⟩
    rw [secondLayer,commutator_secondLayer weight a.val b.val (hP a) (hP b)]
    exact bracket_mem_bracketSpan X _ _ (hfirst a) (hfirst b)
  | one=>
    refine ⟨firstLayer_one weight,?_⟩
    change secondLayer weight (1 : (Matrix I I K)ˣ)∈bracketSpan X
    rw [secondLayer_one]
    exact Submodule.zero_mem _
  | mul u v hu hv ihu ihv=>
    refine ⟨?_,?_⟩
    · change firstLayer weight (u.val*v.val)=0
      rw [firstLayer_mul weight u.val v.val (hP u) (hP v),ihu.1,ihv.1,add_zero]
    · change secondLayer weight (u.val*v.val)∈bracketSpan X
      rw [secondLayer_mul weight u.val v.val (hP u) (hP v) ihu.1]
      exact Submodule.add_mem _ ihu.2 ihv.2
  | inv u hu ihu=>
    refine ⟨?_,?_⟩
    · change firstLayer weight u.val⁻¹=0
      rw [firstLayer_inv weight u.val (hP u),ihu.1,neg_zero]
    · change secondLayer weight u.val⁻¹∈bracketSpan X
      rw [secondLayer_inv weight u.val (hP u) ihu.1]
      exact Submodule.neg_mem _ ihu.2

end SymmetricSubgroupAsymptotics.CFSGGradedMatrixDerivedSecondLayer
