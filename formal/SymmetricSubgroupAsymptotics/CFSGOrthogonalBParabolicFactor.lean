import SymmetricSubgroupAsymptotics.CFSGOrthogonalBFixedMiddleBlock
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGeneralLinearForm
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBArbitraryShearMembership

/-! A literal special B isometry fixing the middle vector and preserving
the positive block factors as its actual GL paired lift followed by an
actual original elementary alternating shear. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBParabolicFactor
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBIndexForm
open CFSGOrthogonalBSpecialFormGroup CFSGOrthogonalBFixedMiddleBlock
open CFSGOrthogonalBGeneralLinearLift CFSGOrthogonalBGeneralLinearForm
open CFSGOrthogonalBIndexShears CFSGMatrixShearUnits
variable (K : Type) [Field K]

theorem fixed_middle_factor (h2 : (2 : K) ≠ 0) (s : ℕ)
    (g : specialFormUnits K (s + 1))
    (hcol : (g.val : Mat K (s + 1)) *ᵥ Pi.single (middle (s + 1)) 1 =
      Pi.single (middle (s + 1)) 1)
    (hnp : ∀ i j, (g.val : Mat K (s + 1)) (neg (s + 1) i) (pos (s + 1) j) = 0) :
    ∃ A : Matrix.GeneralLinearGroup (Fin (s + 1)) K,
      ∃ e : elementaryRootGroup K (s + 1), g.val = generalLinearLift K (s + 1) A * e.val := by
  let f : formUnits K (s + 1) := ⟨g.val, g.property.1⟩
  let M := (g.val : Mat K (s + 1)).toBlocks₁₁
  have hblock : (g.val : Mat K (s + 1)) = Matrix.fromBlocks M 0 0 1 :=
    fixed_middle_block K (s + 1) f hcol
  have hM : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    ext x y
    rcases x with x | x <;> rcases y with y | y
    · rfl
    · rfl
    · exact hnp x y
    · rfl
  have hf := ((mem_specialFormUnits_iff K (s + 1) g.val).mp g.property).1
  have he := congrArg (fun T : Mat K (s + 1) => T.toBlocks₁₁) hf
  simp only [hblock, CFSGOrthogonalBUnipotent.gram_blocks,
    Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.transpose_one,
    Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁] at he
  have hp : (Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂).transpose *
      CFSGHyperbolicTriangularDeterminant.hyperbolicGram *
      Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ =
        CFSGHyperbolicTriangularDeterminant.hyperbolicGram := by
    simpa only [← hM, CFSGHyperbolicTriangularDeterminant.hyperbolicGram,
      Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, one_mul, mul_one] using he
  have hAD := CFSGHyperbolicTriangularDeterminant.diagonal_pairing h2
    M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₂ hp
  have hdet : M.toBlocks₁₁.det ≠ 0 := by
    intro hz
    have hh := congrArg Matrix.det hAD
    rw [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at hh
    exact zero_ne_one hh
  let A := Matrix.GeneralLinearGroup.mkOfDetNeZero M.toBlocks₁₁ hdet
  have hD : M.toBlocks₂₂ =
      ((A⁻¹ : Matrix.GeneralLinearGroup (Fin (s + 1)) K) :
        Matrix (Fin (s + 1)) (Fin (s + 1)) K).transpose := by
    have hh : (A : Matrix (Fin (s + 1)) (Fin (s + 1)) K).transpose * M.toBlocks₂₂ = 1 := hAD
    calc
      M.toBlocks₂₂ =
          (((A⁻¹ : Matrix.GeneralLinearGroup (Fin (s + 1)) K) :
            Matrix (Fin (s + 1)) (Fin (s + 1)) K).transpose *
            (A : Matrix (Fin (s + 1)) (Fin (s + 1)) K).transpose) * M.toBlocks₂₂ := by
        rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, one_mul]
      _ = _ := by rw [mul_assoc, hh, mul_one]
  let C := ((A⁻¹ : Matrix.GeneralLinearGroup (Fin (s + 1)) K) :
    Matrix (Fin (s + 1)) (Fin (s + 1)) K) * M.toBlocks₁₂
  let u := extensionHom K (s + 1) (upper C)
  have hAC : (A : Matrix (Fin (s + 1)) (Fin (s + 1)) K) * C = M.toBlocks₁₂ := by
    dsimp [C]
    rw [← mul_assoc, Units.mul_inv, one_mul]
  have hfactor : generalLinearLift K (s + 1) A * u = g.val := by
    apply Units.ext
    rw [Units.val_mul, generalLinearLift_val, hblock, hM, hD]
    change Matrix.fromBlocks (Matrix.fromBlocks (A : Matrix (Fin (s + 1)) (Fin (s + 1)) K) 0 0
        ((A⁻¹ : Matrix.GeneralLinearGroup (Fin (s + 1)) K) :
          Matrix (Fin (s + 1)) (Fin (s + 1)) K).transpose) 0 0 1 *
      Matrix.fromBlocks (Matrix.fromBlocks 1 C 0 1) 0 0 1 = _
    simp only [Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
      zero_add, add_zero, one_mul, mul_one, hAC]
    rfl
  have huform : u ∈ CFSGOrthogonalBIndexForm.formUnits K (s + 1) := by
    have hu : u = (generalLinearLift K (s + 1) A)⁻¹ * g.val := by rw [← hfactor]; group
    rw [hu]
    exact (formUnits K (s + 1)).mul_mem
      ((formUnits K (s + 1)).inv_mem (generalLinearLift_preserves K (s + 1) A)) g.property.1
  have hualt := CFSGOrthogonalBUnipotent.upperShear_alternating_of_form h2 (s + 1) C huform
  have hu : u ∈ elementaryRootGroup K (s + 1) :=
    CFSGOrthogonalBArbitraryShearMembership.upper_mem K h2 s C hualt.1 hualt.2
  exact ⟨A, ⟨u, hu⟩, hfactor.symm⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBParabolicFactor
