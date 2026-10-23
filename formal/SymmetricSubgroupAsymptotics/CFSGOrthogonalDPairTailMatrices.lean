import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailMatrixEmbedding

/-! A literal matrix fixing both first coordinate axes and retaining
both first coordinate functionals is exactly its tail extension. The
same entry calculation extracts an actual inverse tail matrix unit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDPairTailMatrices
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexTailCoordinates
variable (K : Type) [Field K]

theorem matrix_eq_tail (n : ℕ) (A : Mat K (n + 1))
    (hp : A *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1)
    (hn : A *ᵥ Pi.single (Sum.inr 0) 1 = Pi.single (Sum.inr 0) 1)
    (hrp : ∀ v : Index (n + 1) → K, (A *ᵥ v) (Sum.inl 0) = v (Sum.inl 0))
    (hrn : ∀ v : Index (n + 1) → K, (A *ᵥ v) (Sum.inr 0) = v (Sum.inr 0)) :
    tailMatrixHom K n (A.submatrix (tailIndex n) (tailIndex n)) = A := by
  have hpc (x : Index (n + 1)) : A x (Sum.inl 0) = (Pi.single (Sum.inl (0 : Fin (n + 1))) (1 : K) : Index (n + 1) → K) x := by
    simpa only [Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_apply] using congrFun hp x
  have hnc (x : Index (n + 1)) : A x (Sum.inr 0) = (Pi.single (Sum.inr (0 : Fin (n + 1))) (1 : K) : Index (n + 1) → K) x := by
    simpa only [Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_apply] using congrFun hn x
  have hpr (x : Index (n + 1)) : A (Sum.inl 0) x = (Pi.single x (1 : K) : Index (n + 1) → K) (Sum.inl 0) := by
    simpa only [Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_apply] using hrp (Pi.single x 1)
  have hnr (x : Index (n + 1)) : A (Sum.inr 0) x = (Pi.single x (1 : K) : Index (n + 1) → K) (Sum.inr 0) := by
    simpa only [Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_apply] using hrn (Pi.single x 1)
  ext i j
  obtain ⟨i, rfl⟩ := (tailEquiv n).surjective i
  obtain ⟨j, rfl⟩ := (tailEquiv n).surjective j
  rw [tailMatrixHom_apply_equiv]
  cases i with
  | inl i =>
    cases j with
    | inl j => rfl
    | inr j =>
      fin_cases j
      · change (0 : K) = A (tailIndex n i) (Sum.inl 0)
        rw [hpc]
        cases i <;> simp [tailIndex, Pi.single_apply]
      · change (0 : K) = A (tailIndex n i) (Sum.inr 0)
        rw [hnc]
        cases i <;> simp [tailIndex, Pi.single_apply]
  | inr i =>
    cases j with
    | inl j =>
      fin_cases i
      · change (0 : K) = A (Sum.inl 0) (tailIndex n j)
        rw [hpr]
        cases j <;> simp [tailIndex, Pi.single_apply]
      · change (0 : K) = A (Sum.inr 0) (tailIndex n j)
        rw [hnr]
        cases j <;> simp [tailIndex, Pi.single_apply]
    | inr j =>
      fin_cases i <;> fin_cases j <;>
        simp [tailEquiv_zero, tailEquiv_one, hpc, hnc]

theorem exists_tail_unit (n : ℕ) (u : (Mat K (n + 1))ˣ)
    (hp : (u : Mat K (n + 1)) *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1)
    (hn : (u : Mat K (n + 1)) *ᵥ Pi.single (Sum.inr 0) 1 = Pi.single (Sum.inr 0) 1)
    (hrp : ∀ v : Index (n + 1) → K, ((u : Mat K (n + 1)) *ᵥ v) (Sum.inl 0) = v (Sum.inl 0))
    (hrn : ∀ v : Index (n + 1) → K, ((u : Mat K (n + 1)) *ᵥ v) (Sum.inr 0) = v (Sum.inr 0)) :
    ∃ a : (Mat K n)ˣ, tailUnitHom K n a = u := by
  have hpi : (↑(u⁻¹) : Mat K (n + 1)) *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1 := by
    have h := congrArg (fun v : Index (n + 1) → K =>
      (↑(u⁻¹) : Mat K (n + 1)) *ᵥ v) hp
    dsimp only at h
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h
    exact h.symm
  have hni : (↑(u⁻¹) : Mat K (n + 1)) *ᵥ Pi.single (Sum.inr 0) 1 = Pi.single (Sum.inr 0) 1 := by
    have h := congrArg (fun v : Index (n + 1) → K =>
      (↑(u⁻¹) : Mat K (n + 1)) *ᵥ v) hn
    dsimp only at h
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h
    exact h.symm
  have hrpi (v : Index (n + 1) → K) :
      ((↑(u⁻¹) : Mat K (n + 1)) *ᵥ v) (Sum.inl 0) = v (Sum.inl 0) := by
    have h := hrp ((↑(u⁻¹) : Mat K (n + 1)) *ᵥ v)
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h
    exact h.symm
  have hrni (v : Index (n + 1) → K) :
      ((↑(u⁻¹) : Mat K (n + 1)) *ᵥ v) (Sum.inr 0) = v (Sum.inr 0) := by
    have h := hrn ((↑(u⁻¹) : Mat K (n + 1)) *ᵥ v)
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h
    exact h.symm
  let A := (u : Mat K (n + 1)).submatrix (tailIndex n) (tailIndex n)
  let B := (↑(u⁻¹) : Mat K (n + 1)).submatrix (tailIndex n) (tailIndex n)
  have hA : tailMatrixHom K n A = (u : Mat K (n + 1)) := matrix_eq_tail K n u hp hn hrp hrn
  have hB : tailMatrixHom K n B = (↑(u⁻¹) : Mat K (n + 1)) :=
    matrix_eq_tail K n ↑(u⁻¹) hpi hni hrpi hrni
  have hAB : A * B = 1 := by
    apply tailMatrixHom_injective K n
    rw [map_mul, hA, hB, Units.mul_inv, map_one]
  have hBA : B * A = 1 := by
    apply tailMatrixHom_injective K n
    rw [map_mul, hB, hA, Units.inv_mul, map_one]
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  apply Units.ext
  exact hA

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDPairTailMatrices
