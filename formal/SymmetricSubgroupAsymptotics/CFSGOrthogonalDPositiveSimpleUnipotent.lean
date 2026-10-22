import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveChains
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryElements

/-! Every literal positive simple D root belongs to the same coordinate
unipotent subgroup. This is a matrix support calculation in every field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDPositiveSimpleUnipotent
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDIndexUnipotent CFSGOrthogonalDIndexPositiveChains
variable (K : Type) [Field K]

private theorem single_diag_zero {I : Type*} [DecidableEq I] (i j : I) (hij : i ≠ j)
    (a : K) (x : I) : Matrix.single i j a x x = 0 := by
  have h : ¬(i = x ∧ j = x) := fun h => hij (h.1.trans h.2.symm)
  simp only [Matrix.single_apply, if_neg h]

theorem positive_mem_unipotent (r : ℕ) (i : Fin r) (a : K) :
    rootElement K r false i a ∈ unipotent K r := by
  by_cases hi : i.val + 1 < r
  · let j : Fin r := ⟨i.val + 1, hi⟩
    have hij : i < j := by change i.val < i.val + 1; omega
    have he : ((rootElement K r false i a).val : Mat K r) =
        1 + Matrix.single (Sum.inl i) (Sum.inl j) a -
          Matrix.single (Sum.inr j) (Sum.inr i) a := by
      change 1 + a • positive K r i = _
      rw [positive, dif_pos hi]
      simp only [smul_sub, Matrix.smul_single, smul_eq_mul, mul_one]
      abel
    refine ⟨?_, ?_⟩
    · change ((rootElement K r false i a).val : Mat K r).BlockTriangular (flagEquiv r)
      rw [he]
      apply (Matrix.blockTriangular_one.add (Matrix.blockTriangular_single
        (show flagEquiv r (Sum.inl i) ≤ flagEquiv r (Sum.inl j) from hij.le) a)).sub
      exact Matrix.blockTriangular_single ((flag_neg_lt_neg r j i).mpr hij).le a
    · intro x
      change ((rootElement K r false i a).val : Mat K r) x x = 1
      rw [he]
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply_eq,
        single_diag_zero K _ _ (Sum.inl_injective.ne (ne_of_lt hij)),
        single_diag_zero K _ _ (Sum.inr_injective.ne (ne_of_gt hij)), add_zero, sub_zero]
  · have he : ((rootElement K r false i a).val : Mat K r) =
        1 + Matrix.single (Sum.inl (previous r i)) (Sum.inr i) a -
          Matrix.single (Sum.inl i) (Sum.inr (previous r i)) a := by
      change 1 + a • positive K r i = _
      rw [positive, dif_neg hi]
      simp only [smul_sub, Matrix.smul_single, smul_eq_mul, mul_one]
      abel
    refine ⟨?_, ?_⟩
    · change ((rootElement K r false i a).val : Mat K r).BlockTriangular (flagEquiv r)
      rw [he]
      exact (Matrix.blockTriangular_one.add (Matrix.blockTriangular_single
        (flag_pos_lt_neg r _ _).le a)).sub
        (Matrix.blockTriangular_single (flag_pos_lt_neg r _ _).le a)
    · intro x
      change ((rootElement K r false i a).val : Mat K r) x x = 1
      rw [he]
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply_eq,
        single_diag_zero K _ _ (Sum.inl_ne_inr), add_zero, sub_zero]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDPositiveSimpleUnipotent
