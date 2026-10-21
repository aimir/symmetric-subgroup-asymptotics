import SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

/-! The actual simple coroots in the symplectic matrix realization are
diagonal. Their literal HH Serre relations follow over any commutative ring. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
variable (R : Type*) [CommRing R] (r : ℕ)

theorem cartan_eq (i : Fin r) : cartan R r i =
    if h : i.val + 1 < r then
      (Matrix.single (Sum.inl i) (Sum.inl i) 1 +
        Matrix.single (Sum.inr (⟨i.val + 1, h⟩ : Fin r))
          (Sum.inr (⟨i.val + 1, h⟩ : Fin r)) 1) -
      (Matrix.single (Sum.inl (⟨i.val + 1, h⟩ : Fin r))
          (Sum.inl (⟨i.val + 1, h⟩ : Fin r)) 1 +
        Matrix.single (Sum.inr i) (Sum.inr i) 1)
    else Matrix.single (Sum.inl i) (Sum.inl i) 1 -
      Matrix.single (Sum.inr i) (Sum.inr i) 1 := by
  by_cases h : i.val + 1 < r
  · simp [cartan, negative, positive, h, Ring.lie_def, Matrix.transpose_sub,
      Matrix.transpose_single, sub_mul, mul_sub]
  · simp [cartan, negative, positive, h, Ring.lie_def, Matrix.transpose_single]

theorem cartan_isDiagonal (i : Fin r) :
    ∃ d : Index r → R, cartan R r i = Matrix.diagonal d := by
  rw [cartan_eq]
  split_ifs
  all_goals
    simp only [← Matrix.diagonal_single, Matrix.diagonal_add, Matrix.diagonal_sub]
    exact ⟨_, rfl⟩

theorem cartan_cartan (i j : Fin r) : ⁅cartan R r i, cartan R r j⁆ = 0 := by
  obtain ⟨d, hd⟩ := cartan_isDiagonal R r i
  obtain ⟨e, he⟩ := cartan_isDiagonal R r j
  simp only [hd, he, Ring.lie_def, Matrix.diagonal_mul_diagonal]
  have hde : (fun x => d x * e x) = (fun x => e x * d x) := by
    funext x
    exact mul_comm (d x) (e x)
  rw [hde, sub_self]

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
