import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexGeneralLinearLift
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexShearQuadratic
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveSpace

/-! The SAME-Q positive parabolic factors into its literal paired GL
lift and an actual original alternating-shear word. Preservation of the
quadratic form, not only its polar matrix, proves diagonal zero in
characteristic two. No normality or named group recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexParabolicFactor
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexQuadraticForm
open CFSGOrthogonalDIndexPolarForm CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIsometryIndexGeneralLinearLift
open CFSGOrthogonalDIsometryIndexShearQuadratic CFSGMatrixShearUnits
variable (K : Type) [Field K]

theorem quadratic_preserves_polar (r : ℕ) (g : quadraticPreserving K r)
    (x y : Index r → K) :
    polar K ((g.val : Mat K r) *ᵥ x) ((g.val : Mat K r) *ᵥ y) = polar K x y := by
  have h := g.property (x + y)
  rw [Matrix.mulVec_add, splitQ_add, splitQ_add, g.property x, g.property y] at h
  exact add_left_cancel h

theorem lowerLeft_zero_of_positive_fixed (r : ℕ) (g : (Mat K r)ˣ)
    (hP : (positiveSpace K r).map (Matrix.mulVecLin (g : Mat K r)) = positiveSpace K r) :
    ∀ i j, (g : Mat K r) (Sum.inr i) (Sum.inl j) = 0 := by
  intro i j
  let v : Index r → K := Pi.single (Sum.inl j) 1
  have hv : v ∈ positiveSpace K r := by intro k; simp [v]
  have hh : (g : Mat K r) *ᵥ v ∈ positiveSpace K r := by
    rw [← hP]
    exact ⟨v, hv, rfl⟩
  have he := hh i
  simpa only [v, Matrix.mulVec_single_one, Matrix.col_apply] using he

theorem upperBlock_diagonal_pairing (r : ℕ) (A B D : Matrix (Fin r) (Fin r) K)
    (hQ : ∀ x, splitQ K (Matrix.fromBlocks A B 0 D *ᵥ x) = splitQ K x) :
    A.transpose * D = 1 := by
  have hpolar (x y : Index r → K) :
      polar K (Matrix.fromBlocks A B 0 D *ᵥ x) (Matrix.fromBlocks A B 0 D *ᵥ y) =
        polar K x y := by
    have h := hQ (x + y)
    rw [Matrix.mulVec_add, splitQ_add, splitQ_add, hQ x, hQ y] at h
    exact add_left_cancel h
  have hxy (x y : Fin r → K) : (A *ᵥ x) ⬝ᵥ (D *ᵥ y) = x ⬝ᵥ y := by
    have h := hpolar (Sum.elim x 0) (Sum.elim 0 y)
    simpa only [Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
      Matrix.zero_mulVec, Matrix.mulVec_zero, zero_add, add_zero, polar,
      leftPart, rightPart, zero_dotProduct, dotProduct_zero, add_zero] using h
  ext i j
  have h := hxy (Pi.single i 1) (Pi.single j 1)
  simp only [Matrix.mulVec_single_one, single_dotProduct,
    one_mul, Pi.single_apply] at h
  change (∑ k, A k i * D k j) = if i = j then 1 else 0
  change (∑ k, A k i * D k j) = if i = j then 1 else 0 at h
  exact h

theorem parabolic_factor (s : ℕ) (g : quadraticPreserving K (s + 4))
    (hP : (positiveSpace K (s + 4)).map (Matrix.mulVecLin (g.val : Mat K (s + 4))) =
      positiveSpace K (s + 4)) :
    ∃ A : Matrix.GeneralLinearGroup (Fin (s + 4)) K,
      ∃ e : elementaryRootGroup K (s + 4), g.val = generalLinearLift K (s + 4) A * e.val := by
  let M := (g.val : Mat K (s + 4))
  have hblock : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · rfl
    · exact lowerLeft_zero_of_positive_fixed K (s + 4) g.val hP i j
    · rfl
  have hAD : M.toBlocks₁₁.transpose * M.toBlocks₂₂ = 1 := by
    apply upperBlock_diagonal_pairing K (s + 4) M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₂
    intro x
    rw [← hblock]
    exact g.property x
  have hdet : M.toBlocks₁₁.det ≠ 0 := by
    intro hz
    have hh := congrArg Matrix.det hAD
    rw [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at hh
    exact zero_ne_one hh
  let A := Matrix.GeneralLinearGroup.mkOfDetNeZero M.toBlocks₁₁ hdet
  have hD : M.toBlocks₂₂ =
      ((A⁻¹ : Matrix.GeneralLinearGroup (Fin (s + 4)) K) :
        Matrix (Fin (s + 4)) (Fin (s + 4)) K).transpose := by
    have hh : (A : Matrix (Fin (s + 4)) (Fin (s + 4)) K).transpose * M.toBlocks₂₂ = 1 := hAD
    calc
      M.toBlocks₂₂ =
          (((A⁻¹ : Matrix.GeneralLinearGroup (Fin (s + 4)) K) :
            Matrix (Fin (s + 4)) (Fin (s + 4)) K).transpose *
            (A : Matrix (Fin (s + 4)) (Fin (s + 4)) K).transpose) * M.toBlocks₂₂ := by
        rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, one_mul]
      _ = _ := by rw [mul_assoc, hh, mul_one]
  let C := ((A⁻¹ : Matrix.GeneralLinearGroup (Fin (s + 4)) K) :
    Matrix (Fin (s + 4)) (Fin (s + 4)) K) * M.toBlocks₁₂
  have hAC : (A : Matrix (Fin (s + 4)) (Fin (s + 4)) K) * C = M.toBlocks₁₂ := by
    dsimp only [C]
    rw [← mul_assoc, Units.mul_inv, one_mul]
  have hfactor : generalLinearLift K (s + 4) A * upper C = g.val := by
    apply Units.ext
    rw [Units.val_mul, generalLinearLift_val]
    change Matrix.fromBlocks (A : Matrix (Fin (s + 4)) (Fin (s + 4)) K) 0 0
      ((A⁻¹ : Matrix.GeneralLinearGroup (Fin (s + 4)) K) :
        Matrix (Fin (s + 4)) (Fin (s + 4)) K).transpose * Matrix.fromBlocks 1 C 0 1 = M
    rw [hblock, hD]
    simp only [Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
      zero_add, add_zero, mul_one, hAC]
    rfl
  have huQ : upper C ∈ quadraticPreserving K (s + 4) := by
    have hu : upper C = (generalLinearLift K (s + 4) A)⁻¹ * g.val := by
      rw [← hfactor]
      group
    rw [hu]
    exact (quadraticPreserving K (s + 4)).mul_mem
      ((quadraticPreserving K (s + 4)).inv_mem (generalLinearLift_preserves K (s + 4) A)) g.property
  exact ⟨A, ⟨upper C, upper_mem_of_quadratic K s C huQ⟩, hfactor.symm⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexParabolicFactor
