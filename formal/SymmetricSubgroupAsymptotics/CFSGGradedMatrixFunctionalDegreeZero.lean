import SymmetricSubgroupAsymptotics.CFSGGradedMatrixDistinctDegreeCoordinates

/-! Functional block preservation kills every literal homogeneous degree
on which that functional is nonzero. Applied to independent root
coefficients, this recovers zero coordinates in every characteristic;
no separation of field-valued torus weights is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGGradedMatrixFunctionalDegreeZero
open CFSGGradedMatrixSupport CFSGGradedMatrixSingleDegreeSpan
open CFSGGradedMatrixDistinctDegreeCoordinates

theorem degreePart_eq_zero_of_preserving {I K V W : Type*}
    [CommRing K] [AddCommGroup V] [DecidableEq V] [AddCommGroup W]
    (weight : I→V) (f : V→+W) (d : V) (hd : f d≠0) (M : Matrix I I K)
    (hM : Supported (fun i=>f (weight i)) id M) : degreePart weight d M=0 := by
  ext i j
  change (if weight i=weight j+d then M i j else 0)=0
  by_cases hij : weight i=weight j+d
  · rw [if_pos hij]
    apply hM i j
    intro he
    change f (weight i)=f (weight j) at he
    have hf := congrArg f hij
    rw [map_add] at hf
    have hz : f (weight j)+f d=f (weight j)+0 := by
      rw [←hf,he,add_zero]
    exact hd (add_left_cancel hz)
  · exact if_neg hij

theorem coefficient_eq_zero_of_preserving {I J K V W : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Field K] [AddCommGroup V] [DecidableEq V] [AddCommGroup W]
    (weight : I→V) (f : V→+W) (d : J→V) (hd : Function.Injective d)
    (X : J→Matrix I I K) (hX : ∀j,Supported weight (fun v=>v+d j) (X j))
    (hne : ∀j,X j≠0) (c : J→K)
    (hpres : Supported (fun i=>f (weight i)) id (∑j,c j • X j))
    (j : J) (hfj : f (d j)≠0) : c j=0 := by
  have hs := degreePart_sum weight d hd X hX c j
  have hz := degreePart_eq_zero_of_preserving weight f (d j) hfj
    (∑j,c j • X j) hpres
  exact (smul_eq_zero.mp (hs.symm.trans hz)).resolve_right (hne j)

end SymmetricSubgroupAsymptotics.CFSGGradedMatrixFunctionalDegreeZero
