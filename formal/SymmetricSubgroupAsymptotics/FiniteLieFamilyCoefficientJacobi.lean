import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! A literal coordinate left inverse turns genuine target Lie action
identities into the mixed coefficient identity required by the original
Serre source lowering induction. No injectivity of the source realization
is involved. This replaces rank-dependent coefficient expansion by Jacobi. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteLieFamilyCoefficientJacobi
variable {I J L : Type*} [Fintype J] [DecidableEq J] [DecidableEq I]
    [LieRing L] [LieAlgebra ℚ L]
    (v : J→L) (c : L→ₗ[ℚ](J→ℚ))
    (hcoord : ∀ j,c (v j)=Pi.single j 1)

include hcoord

private theorem coordinates_combination (q : J→ℚ) :
    c (Fintype.linearCombination ℚ v q)=q := by
  rw [Fintype.linearCombination_apply]
  rw [map_sum]
  simp only [map_smul,hcoord]
  funext j
  simp [Finset.sum_apply,hcoord,Pi.single_apply]

private theorem coordinates_lie_combination (z : L) (row : J→J→ℚ)
    (q : J→ℚ)
    (hz : ∀ j,q j≠0→⁅z,v j⁆=Fintype.linearCombination ℚ v (row j)) :
    c ⁅z,Fintype.linearCombination ℚ v q⁆=
      Fintype.linearCombination ℚ row q := by
  simp only [Fintype.linearCombination_apply]
  rw [lie_sum,map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hq : q j=0
  · simp only [hq,zero_smul,lie_zero,map_zero]
  · rw [lie_smul,map_smul,hz j hq,coordinates_combination v c hcoord]

theorem mixed_coefficients (U V H : I→L)
    (e f : I→J→J→ℚ) (weight : I→J→ℚ)
    (hE : ∀ i j,⁅U i,v j⁆=Fintype.linearCombination ℚ v (e i j))
    (hEF : ∀ a i,⁅V a,U i⁆=if a=i then -H a else 0)
    (hweight : ∀ a j,⁅H a,v j⁆=weight a j • v j) (i a : I) (j : J)
    (hFj : ⁅V a,v j⁆=Fintype.linearCombination ℚ v (f a j))
    (hFE : ∀ l,e i j l≠0→⁅V a,v l⁆=Fintype.linearCombination ℚ v (f a l)) :
    (if a=i then (-weight a j) • Pi.single j 1 else 0)+
      (∑ l,f a j l • e i l)=Fintype.linearCombination ℚ (f a) (e i j) := by
  classical
  symm
  calc
    Fintype.linearCombination ℚ (f a) (e i j) = c ⁅V a,⁅U i,v j⁆⁆ := by
      rw [hE,coordinates_lie_combination v c hcoord _ _ _ hFE]
    _ = c ⁅⁅V a,U i⁆,v j⁆ + c ⁅U i,⁅V a,v j⁆⁆ := by
      rw [leibniz_lie,map_add]
    _ = _ := by
      rw [hEF,hFj,coordinates_lie_combination v c hcoord _ _ _ (fun l _ => hE i l)]
      by_cases h : a=i
      · simp only [if_pos h,neg_lie,hweight,map_neg,map_smul,hcoord,
          neg_smul,Fintype.linearCombination_apply]
      · simp only [if_neg h,zero_lie,map_zero,zero_add,
          Fintype.linearCombination_apply]

end SymmetricSubgroupAsymptotics.FiniteLieFamilyCoefficientJacobi
