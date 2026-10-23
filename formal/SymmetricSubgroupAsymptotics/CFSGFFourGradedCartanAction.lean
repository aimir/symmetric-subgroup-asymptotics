import SymmetricSubgroupAsymptotics.CFSGGradedMatrixDistinctDegreeCoordinates
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.Ring

/-! Entrywise Cartan separation for literal graded matrices. Distinct
INTEGRAL degrees are projected before coefficient reduction; a primitive
Cartan weight can therefore detect a root coordinate in every field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGFFourGradedCartanAction
open CFSGGradedMatrixSupport CFSGGradedMatrixSingleDegreeSpan
open CFSGGradedMatrixDistinctDegreeCoordinates
variable {I V K : Type*} [Fintype I] [DecidableEq I] [AddCommGroup V]
    [DecidableEq V] [Field K]

def cartanDiagonal (weight : I → V) (f : V →+ ℤ) : Matrix I I K :=
  Matrix.diagonal (fun i=>(f (weight i) : K))

theorem diagonal_lie_homogeneous (weight : I → V) (f : V →+ ℤ)
    (d : V) (M : Matrix I I K) (hM : Supported weight (fun v=>v+d) M) :
    ⁅cartanDiagonal (K:=K) weight f,M⁆ = (f d : K) • M := by
  ext i j
  simp only [Ring.lie_def,cartanDiagonal,Matrix.sub_apply,Matrix.diagonal_mul,
    Matrix.mul_diagonal,Matrix.smul_apply,smul_eq_mul]
  by_cases he : weight i=weight j+d
  · rw [he,map_add,Int.cast_add]
    ring
  · rw [hM i j he]
    simp

theorem degreePart_diagonal_lie (weight : I → V) (d : V) (a : I → K)
    (M : Matrix I I K) :
    degreePart weight d ⁅Matrix.diagonal a,M⁆ =
      ⁅Matrix.diagonal a,degreePart weight d M⁆ := by
  ext i j
  by_cases he : weight i=weight j+d <;>
    simp [degreePart,Ring.lie_def,Matrix.diagonal_mul,Matrix.mul_diagonal,he]

theorem degreePart_lie_zero_of_commute (weight : I → V) (d : V)
    (a : I → K) (M : Matrix I I K) (hc : Commute (Matrix.diagonal a) M) :
    ⁅Matrix.diagonal a,degreePart weight d M⁆ = 0 := by
  have hz : ⁅Matrix.diagonal a,M⁆ = 0 := sub_eq_zero.mpr hc.eq
  have h := congrArg (degreePart weight d) hz
  rw [degreePart_diagonal_lie,map_zero] at h
  exact h

theorem homogeneous_coordinate_zero {J : Type*} [Fintype J] [DecidableEq J]
    (weight : I → V) (f : V →+ ℤ) (d : J → V) (hd : Function.Injective d)
    (X : J → Matrix I I K) (hX : ∀j,Supported weight (fun v=>v+d j) (X j))
    (c : J → K) (hc : ⁅cartanDiagonal (K:=K) weight f,∑j,c j • X j⁆ = 0)
    (k : J) (hk : X k≠0) (hf : (f (d k) : K)≠0) : c k=0 := by
  have hx (j : J) : ⁅cartanDiagonal (K:=K) weight f,X j⁆ = (f (d j) : K) • X j :=
    diagonal_lie_homogeneous weight f (d j) (X j) (hX j)
  have hs : (∑j,(c j * (f (d j) : K)) • X j)=0 := by
    simpa only [lie_sum,lie_smul,hx,smul_smul] using hc
  have hp := congrArg (degreePart weight (d k)) hs
  rw [degreePart_sum weight d hd X hX (fun j=>c j * (f (d j) : K)) k,map_zero] at hp
  have hm : c k * (f (d k) : K)=0 := (smul_eq_zero.mp hp).resolve_right hk
  exact (mul_eq_zero.mp hm).resolve_right hf

end SymmetricSubgroupAsymptotics.CFSGFFourGradedCartanAction
