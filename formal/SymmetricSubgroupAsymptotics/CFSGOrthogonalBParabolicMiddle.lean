import SymmetricSubgroupAsymptotics.CFSGOrthogonalBParabolicColumn
import SymmetricSubgroupAsymptotics.CFSGHyperbolicTriangularDeterminant
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUpperShearForm

/-! After clearing the middle column of an actual special isometry
stabilizing V⁺, the middle scalar is exactly one. This follows from
literal block determinants, not a named SO/Omega identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBParabolicMiddle
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBSpecialFormGroup
open CFSGOrthogonalBParabolicColumn CFSGOrthogonalBIndexForm
variable (K : Type) [Field K]

theorem middle_scalar_eq_one (h2 : (2 : K) ≠ 0) (n : ℕ)
    (g : specialFormUnits K n) (c : K)
    (hcol : (g.val : Mat K n) *ᵥ Pi.single (middle n) 1 =
      c • Pi.single (middle n) 1)
    (hnp : ∀ i j, (g.val : Mat K n) (neg n i) (pos n j) = 0) : c = 1 := by
  let f : formUnits K n := ⟨g.val, g.property.1⟩
  let e : Index n → K := Pi.single (middle n) 1
  have hc : c ≠ 0 := by
    intro hc
    have hh := pairing_invariant K n f e e
    change (gram K n).toBilin' ((g.val : Mat K n) *ᵥ e)
      ((g.val : Mat K n) *ᵥ e) = (gram K n).toBilin' e e at hh
    change (g.val : Mat K n) *ᵥ e = c • e at hcol
    rw [hcol, hc, zero_smul] at hh
    simp [e, gram, middle] at hh
  have hrow (j : Fin n ⊕ Fin n) : (g.val : Mat K n) (middle n) (Sum.inl j) = 0 := by
    have hh := pairing_invariant K n f (Pi.single (Sum.inl j) 1) e
    change (gram K n).toBilin' ((g.val : Mat K n) *ᵥ Pi.single (Sum.inl j) 1)
      ((g.val : Mat K n) *ᵥ e) = _ at hh
    change (g.val : Mat K n) *ᵥ e = c • e at hcol
    rw [hcol, map_smul, pairing_middle, pairing_middle] at hh
    have hz : c * (g.val : Mat K n) (middle n) (Sum.inl j) = 0 := by
      simpa [e, Matrix.mulVec_single_one, Matrix.col, middle, Pi.single_apply] using hh
    exact (mul_eq_zero.mp hz).resolve_left hc
  let M := (g.val : Mat K n).toBlocks₁₁
  have hblock : (g.val : Mat K n) = Matrix.fromBlocks M 0 0
      (c • (1 : Matrix Unit Unit K)) := by
    ext x y
    rcases x with x | ⟨⟩ <;> rcases y with y | ⟨⟩
    · rfl
    · have hh := congrFun hcol (Sum.inl x)
      simpa [Matrix.mulVec_single_one, Matrix.col, Matrix.fromBlocks, middle, Pi.single_apply] using hh
    · exact hrow y
    · have hh := congrFun hcol (middle n)
      simpa [Matrix.mulVec_single_one, Matrix.col, Matrix.fromBlocks, middle, Pi.single_apply] using hh
  have hM : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    ext x y
    rcases x with x | x <;> rcases y with y | y
    · rfl
    · rfl
    · exact hnp x y
    · rfl
  have hform := ((mem_specialFormUnits_iff K n g.val).mp g.property).1
  have he := congrArg (fun T : Mat K n => T.toBlocks₁₁) hform
  simp only [hblock, CFSGOrthogonalBUnipotent.gram_blocks,
    Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.fromBlocks_multiply,
    Matrix.toBlocks_fromBlocks₁₁] at he
  have hMdet : M.det = 1 := by
    have hp : (Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂).transpose *
        CFSGHyperbolicTriangularDeterminant.hyperbolicGram *
        Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ =
          CFSGHyperbolicTriangularDeterminant.hyperbolicGram := by
      simpa only [← hM, CFSGHyperbolicTriangularDeterminant.hyperbolicGram,
        Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add] using he
    have hh := CFSGHyperbolicTriangularDeterminant.determinant_eq_one h2
      M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₂ hp
    simpa only [← hM] using hh
  have hd := ((mem_specialFormUnits_iff K n g.val).mp g.property).2
  rw [hblock, Matrix.det_fromBlocks_zero₂₁, hMdet, one_mul] at hd
  simpa using hd

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBParabolicMiddle
