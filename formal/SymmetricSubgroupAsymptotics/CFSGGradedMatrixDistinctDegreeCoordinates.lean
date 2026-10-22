import SymmetricSubgroupAsymptotics.CFSGGradedMatrixSingleDegreeSpan

/-! Literal lattice-degree projections recover coefficients in a finite
family of nonzero operators in distinct degrees. This separation does not
use torus eigenvalues and hence survives bad characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGradedMatrixDistinctDegreeCoordinates
open CFSGGradedMatrixSupport CFSGGradedMatrixSingleDegreeSpan
variable {I J K V : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Field K] [AddCommGroup V] [DecidableEq V]

theorem degreePart_sum (weight : I→V) (d : J→V) (hd : Function.Injective d)
    (X : J→Matrix I I K)
    (hX : ∀j,Supported weight (fun v=>v+d j) (X j)) (c : J→K) (j₀ : J) :
    degreePart weight (d j₀) (∑j,c j • X j)=c j₀ • X j₀ := by
  rw [map_sum]
  simp only [map_smul]
  calc
    _=∑j,if j=j₀ then c j • X j else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases heq : j=j₀
      · subst j
        rw [if_pos rfl,degreePart_eq weight (d j₀) (X j₀) (hX j₀)]
      · rw [if_neg heq,degreePart_zero_of_other weight (d j₀) (d j) (X j) (hX j)
          (fun h=>heq (hd h).symm),smul_zero]
    _=_ := by simp

theorem coefficients_unique (weight : I→V) (d : J→V) (hd : Function.Injective d)
    (X : J→Matrix I I K)
    (hX : ∀j,Supported weight (fun v=>v+d j) (X j)) (hne : ∀j,X j≠0)
    (c e : J→K) (h : (∑j,c j • X j)=∑j,e j • X j) : c=e := by
  funext j
  have hh := congrArg (degreePart weight (d j)) h
  rw [degreePart_sum weight d hd X hX c j,degreePart_sum weight d hd X hX e j] at hh
  have hz : (c j-e j) • X j=0 := by rw [sub_smul,hh,sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right (hne j))

end SymmetricSubgroupAsymptotics.CFSGGradedMatrixDistinctDegreeCoordinates
