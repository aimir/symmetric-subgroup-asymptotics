import SymmetricSubgroupAsymptotics.CFSGOrthogonalBZeroMiddleKernel
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGeneralLinearForm

/-! The nonidentity possibility in the zero-middle-point kernel is
represented by an ACTUAL determinant-one isometry of the SAME original
natural space. Thus the kernel theorem introduces no extra independent
factor beyond the checked special-isometry/elementary index. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBMiddleFlipSpecial
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBSpecialFormGroup
open CFSGOrthogonalBGeneralLinearLift CFSGOrthogonalBGeneralLinearForm
open CFSGPolarSubspacePoints CFSGSingularPlaneTriangle
open CFSGOrthogonalBZeroMiddleScalarCoupling
variable (K : Type) [Field K]

def scalarMinus (n : ℕ) : Matrix.GeneralLinearGroup (Fin n) K :=
  CFSGMatrixDiagonalBlockLift.diagonalUnit (fun _ => (-1 : Kˣ))

def flipUnit (n : ℕ) : (Mat K n)ˣ := generalLinearLift K n (scalarMinus K n)

theorem flipUnit_val (n : ℕ) :
    (flipUnit K n : Mat K n) =
      Matrix.fromBlocks (Matrix.fromBlocks (-1) 0 0 (-1)) 0 0 1 := by
  have hA : (scalarMinus K n : Matrix (Fin n) (Fin n) K) = -1 := by
    ext i j
    by_cases hij : i = j <;> simp [hij, scalarMinus, CFSGMatrixDiagonalBlockLift.diagonalUnit,
      Matrix.diagonal_apply, Matrix.one_apply]
  have hAi : ((scalarMinus K n)⁻¹ : Matrix.GeneralLinearGroup (Fin n) K).val = -1 := by
    ext i j
    by_cases hij : i = j <;> simp [hij, scalarMinus, CFSGMatrixDiagonalBlockLift.diagonalUnit,
      Matrix.diagonal_apply, Matrix.one_apply]
  change (generalLinearLift K n (scalarMinus K n) : Mat K n) = _
  rw [generalLinearLift_val, hA, hAi, Matrix.transpose_neg, Matrix.transpose_one]

theorem flipUnit_mem_special (n : ℕ) : flipUnit K n ∈ specialFormUnits K n :=
  generalLinearLift_mem_special K n (scalarMinus K n)

theorem flipUnit_action (n : ℕ) (v : Index n → K) :
    (flipUnit K n : Mat K n) *ᵥ v = CFSGOrthogonalBMiddleFlip.vectorEquiv K n v := by
  rw [flipUnit_val]
  funext i
  rcases i with (i | i) | ⟨⟩
  all_goals simp [Matrix.fromBlocks_mulVec, Matrix.neg_mulVec, middle,
    CFSGOrthogonalBMiddleFlip.vectorEquiv]

theorem flipUnit_linearMap (n : ℕ) :
    (flipUnit K n : Mat K n).mulVecLin =
      (CFSGOrthogonalBMiddleFlip.vectorEquiv K n).toLinearMap := by
  apply LinearMap.ext
  intro v
  exact flipUnit_action K n v

variable [Finite K]

theorem zero_middle_kernel_is_special_action (h2 : (2 : K) ≠ 0) (s : ℕ)
    (f : Points (Form K s) ≃ Points (Form K s))
    (horth : ∀ P Q, ZeroOn (Form K s) (f P).val (f Q).val ↔ ZeroOn (Form K s) P.val Q.val)
    (hfix : ∀ R : Points (Form K s), (∀ z ∈ R.val, z (middle (s + 3)) = 0) → f R = R) :
    ∃ g : specialFormUnits K (s + 3), ∀ P : Points (Form K s),
      (f P).val = P.val.map (g.val : Mat K (s + 3)).mulVecLin := by
  rcases CFSGOrthogonalBZeroMiddleKernel.eq_identity_or_middle_flip K h2 s f horth hfix with
    he | he
  · refine ⟨1, ?_⟩
    intro P
    rw [he]
    change P.val = P.val.map (1 : Mat K (s + 3)).mulVecLin
    rw [Matrix.mulVecLin_one, Submodule.map_id]
  · refine ⟨⟨flipUnit K (s + 3), flipUnit_mem_special K (s + 3)⟩, ?_⟩
    intro P
    rw [he]
    change P.val.map (CFSGOrthogonalBMiddleFlip.vectorEquiv K (s + 3)).toLinearMap =
      P.val.map (flipUnit K (s + 3) : Mat K (s + 3)).mulVecLin
    rw [flipUnit_linearMap]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBMiddleFlipSpecial
