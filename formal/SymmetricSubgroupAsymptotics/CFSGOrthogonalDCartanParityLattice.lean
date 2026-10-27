import SymmetricSubgroupAsymptotics.CFSGOrthogonalDCartanMatrices
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Ring

/-! The intrinsic integral diagonal lattice for the literal D realization.
The terminal simple coroot has coordinate sum 2, while chain coroots have
sum 0. Ambient integer diagonal coordinates are therefore not a primitive
Cartan coordinate system. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDCartanParityLattice
open CFSGOrthogonalDSerreMatrices
variable (r : ℕ)

def evenSum : Submodule ℤ (Fin r→ℤ) where
  carrier := {a | ∃ z : ℤ,∑ i,a i=2*z}
  zero_mem' := ⟨0,by simp⟩
  add_mem' := by
    rintro a b ⟨u,hu⟩ ⟨v,hv⟩
    refine ⟨u+v,?_⟩
    simp only [Pi.add_apply,Finset.sum_add_distrib,hu,hv]
    ring
  smul_mem' := by
    rintro z a ⟨u,hu⟩
    refine ⟨z*u,?_⟩
    simp only [Pi.smul_apply,smul_eq_mul,←Finset.mul_sum,hu]
    ring

def column (i : Fin r) : Fin r→ℤ := fun j=>cartan ℤ r i (.inl j) (.inl j)

theorem column_sum (hr : 4 ≤ r) (i : Fin r) :
    (∑ j,column r i j)=if i.val+1 < r then 0 else 2 := by
  unfold column
  rw [cartan_eq ℤ r hr]
  split_ifs with h
  · simp [Matrix.add_apply,Matrix.sub_apply,Matrix.single_apply,
      Finset.sum_add_distrib,Finset.sum_sub_distrib]
  · simp [Matrix.add_apply,Matrix.sub_apply,Matrix.single_apply,
      Finset.sum_add_distrib,Finset.sum_sub_distrib]

theorem column_mem (hr : 4 ≤ r) (i : Fin r) : column r i∈evenSum r := by
  change ∃ z : ℤ,∑ j,column r i j=2*z
  rw [column_sum r hr i]
  split_ifs
  · exact ⟨0,by norm_num⟩
  · exact ⟨1,by norm_num⟩

theorem combination_mem (hr : 4 ≤ r) (a : Fin r→ℤ) :
    Fintype.linearCombination ℤ (column r) a∈evenSum r := by
  rw [Fintype.linearCombination_apply]
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (column_mem r hr i)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDCartanParityLattice
