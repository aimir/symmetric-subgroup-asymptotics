import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationInitialRootMatrices
import SymmetricSubgroupAsymptotics.CFSGDiagonalUnitRootAction

/-! Exact diagonal weights on the two initial D root lines. The torus
fixes e1-e0 and scales e1+e_last by its primitive field parameter, not its
square. In particular this step does not discard the three-element field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationInitialDiagonalAction
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationInitialElements
open CFSGOrthogonalDGenerationInitialRootMatrices CFSGOrthogonalDGenerationForkTorus
variable (K : Type) [Field K]

private theorem sparse_root_conjugation {I : Type*} [Fintype I] [DecidableEq I]
    (T : (Matrix I I K)ˣ) (root : K → (Matrix I I K)ˣ)
    (d : I → K) (hT : (T : Matrix I I K) = Matrix.diagonal d)
    (i j k l : I)
    (hroot : ∀ a, (root a : Matrix I I K) = 1 + Matrix.single i j a - Matrix.single k l a)
    (c a : K) (hp : d i = c * d j) (hn : d k = c * d l) :
    T * root a * T⁻¹ = root (c * a) := by
  have hr (b : K) : (root b : Matrix I I K) =
      1 + b • (Matrix.single i j 1 - Matrix.single k l 1) := by
    rw [hroot]
    simp only [smul_sub, Matrix.smul_single, smul_eq_mul, mul_one]
    abel
  apply CFSGDiagonalUnitRootAction.root_line_conjugation T (root a) (root (c * a))
    d (Matrix.single i j 1 - Matrix.single k l 1) c a hT (hr a) (hr (c * a))
  intro x y hX
  by_cases hpos : i = x ∧ j = y
  · rcases hpos with ⟨rfl, rfl⟩
    exact hp
  · by_cases hneg : k = x ∧ l = y
    · rcases hneg with ⟨rfl, rfl⟩
      exact hn
    · have hz : (Matrix.single i j 1 - Matrix.single k l 1 : Matrix I I K) x y = 0 := by
        simp only [Matrix.sub_apply, Matrix.single_apply, hpos, hneg, if_false, sub_self]
      exact (hX hz).elim

theorem initialShort_diagonal_conjugation (s : ℕ)
    (T : elementaryRootGroup K (s + 4)) (d : Index (s + 4) → K)
    (hT : (T.val : Mat K (s + 4)) = Matrix.diagonal d) (c a : K)
    (hp : d (Sum.inl (second s)) = c * d (Sum.inl 0))
    (hn : d (Sum.inr (0 : Fin (s + 4))) = c * d (Sum.inr (second s))) :
    T * initialShortRoot K s a * T⁻¹ = initialShortRoot K s (c * a) := by
  apply Subtype.ext
  exact sparse_root_conjugation K T.val (fun b => (initialShortRoot K s b).val)
    d hT _ _ _ _ (initialShortRoot_coe K s) c a hp hn

theorem initialStar_diagonal_conjugation (s : ℕ)
    (T : elementaryRootGroup K (s + 4)) (d : Index (s + 4) → K)
    (hT : (T.val : Mat K (s + 4)) = Matrix.diagonal d) (c a : K)
    (hp : d (Sum.inl (second s)) = c * d (Sum.inr (last (s + 2))))
    (hn : d (Sum.inl (last (s + 2))) = c * d (Sum.inr (second s))) :
    T * initialStarRoot K s false a * T⁻¹ = initialStarRoot K s false (c * a) := by
  apply Subtype.ext
  exact sparse_root_conjugation K T.val (fun b => (initialStarRoot K s false b).val)
    d hT _ _ _ _ (fun b => by
      simpa only [Bool.false_eq_true, if_false] using (initialStarRoot_coe K s false b)) c a hp hn

theorem torusPermutation_zero (s : ℕ) : torusPermutation s 0 = pen (s + 2) := by
  simp [torusPermutation, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    Ne.symm (second_ne_zero s), Ne.symm (last_ne_zero s)]

theorem torusPermutation_second (s : ℕ) : torusPermutation s (second s) = last (s + 2) := by
  simp [torusPermutation, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    last_ne_zero, Ne.symm (pen_ne_last (s + 2))]

theorem torusPermutation_last (s : ℕ) : torusPermutation s (last (s + 2)) = second s := by
  simp [torusPermutation, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    second_ne_zero, second_ne_pen]

theorem initialTorusDiagonal_values (s : ℕ) (g : Kˣ) :
    initialTorusDiagonal K s g (Sum.inl 0) = (g : K) ∧
    initialTorusDiagonal K s g (Sum.inl (second s)) = (g : K) ∧
    initialTorusDiagonal K s g (Sum.inr 0) = (g : K)⁻¹ ∧
    initialTorusDiagonal K s g (Sum.inr (second s)) = (g : K)⁻¹ ∧
    initialTorusDiagonal K s g (Sum.inl (last (s + 2))) = 1 ∧
    initialTorusDiagonal K s g (Sum.inr (last (s + 2))) = 1 := by
  simp [initialTorusDiagonal, torusPermutation_zero, torusPermutation_second,
    torusPermutation_last, forkDiagonal, second_ne_pen, second_ne_last]

theorem initialTorus_short_conjugation (s : ℕ) (g : Kˣ) (a : K) :
    initialTorus K s g * initialShortRoot K s a * (initialTorus K s g)⁻¹ =
      initialShortRoot K s a := by
  have hv := initialTorusDiagonal_values K s g
  have h := initialShort_diagonal_conjugation K s (initialTorus K s g)
    (initialTorusDiagonal K s g) (initialTorus_coe K s g) 1 a
    (by rw [hv.1, hv.2.1, one_mul])
    (by rw [hv.2.2.1, hv.2.2.2.1, one_mul])
  simpa only [one_mul] using h

theorem initialTorus_star_conjugation (s : ℕ) (g : Kˣ) (a : K) :
    initialTorus K s g * initialStarRoot K s false a * (initialTorus K s g)⁻¹ =
      initialStarRoot K s false ((g : K) * a) := by
  have hv := initialTorusDiagonal_values K s g
  apply initialStar_diagonal_conjugation K s (initialTorus K s g)
    (initialTorusDiagonal K s g) (initialTorus_coe K s g)
  · rw [hv.2.1, hv.2.2.2.2.2, mul_one]
  · rw [hv.2.2.2.2.1, hv.2.2.2.1, mul_inv_cancel₀ (Units.ne_zero g)]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationInitialDiagonalAction
