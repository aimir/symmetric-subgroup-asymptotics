import SymmetricSubgroupAsymptotics.CFSGGradedMatrixSubgroups

/-! Opposite strict matrix groups cannot have the same nontrivial action
on a diagonal Cartan. The statement concerns their literal conjugation
of matrices, not faithfulness of either whole ambient action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourOppositeCartanActions
open CFSGGradedMatrixSubgroups
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

theorem strict_conjugate_diagonal_entry (weight : I → ℤ) (u : (Matrix I I K)ˣ)
    (hu : u∈strictUnits weight) (d : I → K) (i j : I) (hij : weight i≤weight j) :
    ((u : Matrix I I K) * Matrix.diagonal d * (↑(u⁻¹) : Matrix I I K)) i j =
      (Matrix.diagonal d) i j := by
  have hinv := (strictUnits weight).inv_mem hu
  rw [Matrix.mul_apply]
  calc
    (∑t,((u : Matrix I I K) * Matrix.diagonal d) i t *
        (↑(u⁻¹) : Matrix I I K) t j) =
      ((u : Matrix I I K) * Matrix.diagonal d) i i *
        (↑(u⁻¹) : Matrix I I K) i j := by
      apply Finset.sum_eq_single i
      · intro t _ hti
        rw [Matrix.mul_diagonal]
        by_cases hit : weight i≤weight t
        · rw [hu i t hit,Matrix.one_apply,if_neg (Ne.symm hti),zero_mul,zero_mul]
        · have htj : weight t≤weight j := by omega
          have hne : t≠j := by intro he;subst t;omega
          rw [hinv t j htj,Matrix.one_apply,if_neg hne,mul_zero]
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
    _ = (Matrix.diagonal d) i j := by
      rw [Matrix.mul_diagonal,hu i i le_rfl,Matrix.one_apply_eq,one_mul,hinv i j hij]
      by_cases he : i=j <;> simp [Matrix.one_apply,he]

theorem opposite_equal_cartan_action_fixes (weight : I → ℤ)
    (u v : (Matrix I I K)ˣ) (hu : u∈strictUnits weight)
    (hv : v∈strictUnits (fun i=> -weight i)) (d : I → K)
    (he : (u : Matrix I I K) * Matrix.diagonal d * (↑(u⁻¹) : Matrix I I K) =
      (v : Matrix I I K) * Matrix.diagonal d * (↑(v⁻¹) : Matrix I I K)) :
    (u : Matrix I I K) * Matrix.diagonal d * (↑(u⁻¹) : Matrix I I K) = Matrix.diagonal d := by
  ext i j
  by_cases hij : weight i≤weight j
  · exact strict_conjugate_diagonal_entry weight u hu d i j hij
  · rw [he]
    exact strict_conjugate_diagonal_entry (fun a=> -weight a) v hv d i j (by
      change -weight i ≤ -weight j
      omega)

end SymmetricSubgroupAsymptotics.CFSGFFourOppositeCartanActions
