import SymmetricSubgroupAsymptotics.CFSGHermitianIsometryDeterminant
import Mathlib.Data.Matrix.Block

/-! The literal determinant-corrected block hom from GL(I,K) to
SL(I+1,K). It is injective, and takes identity-form Hermitian isometries
to identity-form Hermitian isometries. No group order or named-model
identification is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.HermitianDeterminantCorrection
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

/-- The last scalar corrects the determinant of the SAME original matrix. -/
def matrix (A : (Matrix I I K)ˣ) : Matrix (I ⊕ Unit) (I ⊕ Unit) K :=
  Matrix.fromBlocks (A : Matrix I I K) 0 0 (fun _ _ : Unit =>
    (Matrix.det (A : Matrix I I K))⁻¹)

theorem determinant_one (A : (Matrix I I K)ˣ) : Matrix.det (matrix A) = 1 := by
  rw [matrix, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_unique (fun _ _ : Unit => (Matrix.det (A : Matrix I I K))⁻¹)]
  exact mul_inv_cancel₀ (Matrix.GeneralLinearGroup.det_ne_zero A)

/-- This is a hom on the FULL general linear group, before any restriction
to unitary matrices, so all original conjugation identities are retained. -/
def hom : (Matrix I I K)ˣ →* Matrix.SpecialLinearGroup (I ⊕ Unit) K where
  toFun A := ⟨matrix A, determinant_one A⟩
  map_one' := by
    apply Subtype.ext
    funext i j
    cases i <;> cases j <;> simp [matrix, Matrix.fromBlocks, Matrix.one_apply]
  map_mul' A B := by
    apply Subtype.ext
    change Matrix.fromBlocks ((A : Matrix I I K)*(B : Matrix I I K)) 0 0
      (fun _ _ : Unit => (Matrix.det ((A : Matrix I I K)*(B : Matrix I I K)))⁻¹) =
      Matrix.fromBlocks (A : Matrix I I K) 0 0
        (fun _ _ : Unit => (Matrix.det (A : Matrix I I K))⁻¹) *
      Matrix.fromBlocks (B : Matrix I I K) 0 0
        (fun _ _ : Unit => (Matrix.det (B : Matrix I I K))⁻¹)
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    apply Matrix.fromBlocks_inj.mpr
    refine ⟨rfl,rfl,rfl,?_⟩
    funext i j
    simp [Matrix.mul_apply, Matrix.det_mul, mul_inv_rev, mul_comm]

theorem hom_injective : Function.Injective (hom (K := K) (I := I)) := by
  intro A B h
  apply Units.ext
  funext i j
  exact congrArg (fun C : Matrix.SpecialLinearGroup (I ⊕ Unit) K =>
    C.val (Sum.inl i) (Sum.inl j)) h

theorem preserves_identity_form (sigma : K ≃+* K) (A : (Matrix I I K)ˣ)
    (hA : ((A : Matrix I I K).map sigma).transpose*(A : Matrix I I K)=1) :
    ((hom A).val.map sigma).transpose*(hom A).val=1 := by
  have hdet : sigma (Matrix.det (A : Matrix I I K))*
      Matrix.det (A : Matrix I I K)=1 := by
    have hd := congrArg Matrix.det hA
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hd
    have hmap : Matrix.det ((A : Matrix I I K).map sigma)=
        sigma (Matrix.det (A : Matrix I I K)) :=
      (RingHom.map_det sigma.toRingHom (A : Matrix I I K)).symm
    rw [hmap] at hd
    exact hd
  have hinv : sigma ((Matrix.det (A : Matrix I I K))⁻¹)*
      (Matrix.det (A : Matrix I I K))⁻¹=1 := by
    rw [map_inv₀, ← mul_inv, hdet, inv_one]
  change ((matrix A).map sigma).transpose*matrix A=1
  rw [matrix, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.map_zero sigma (map_zero sigma), Matrix.transpose_zero, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, hA]
  rw [← Matrix.fromBlocks_one]
  apply Matrix.fromBlocks_inj.mpr
  refine ⟨rfl,rfl,rfl,?_⟩
  funext i j
  simpa only [Matrix.mul_apply, Fintype.sum_unique, Matrix.map_apply,
    Matrix.transpose_apply, Matrix.one_apply, if_pos (Subsingleton.elim i j)] using hinv

end SymmetricSubgroupAsymptotics.HermitianDeterminantCorrection
