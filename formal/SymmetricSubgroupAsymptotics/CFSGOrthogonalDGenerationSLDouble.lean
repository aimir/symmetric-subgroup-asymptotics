import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationAdjacentSL
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDElementaryGroup
import Mathlib.Data.Matrix.Block

/-! The literal natural embedding A ↦ diag(A,A⁻ᵀ) belongs to the actual
D elementary root subgroup. Membership is proved from adjacent original
D roots and the preceding SL chain generation theorem. No equality with
a full orthogonal group is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSLDouble
open Matrix CFSGOrthogonalDSerreMatrices CFSGTypeAElementaryMatrices
variable (K : Type) [Field K] (r : ℕ)

abbrev NaturalSL := Matrix.SpecialLinearGroup (Fin r) K

def doubleMatrix (A : NaturalSL K r) : Mat K r :=
  Matrix.fromBlocks A.val 0 0 ((A⁻¹).val.transpose)

theorem doubleMatrix_one : doubleMatrix K r 1 = 1 := by
  unfold doubleMatrix
  rw [inv_one]
  change Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) K) 0 0 (1 : Matrix (Fin r) (Fin r) K).transpose = 1
  rw [Matrix.transpose_one, Matrix.fromBlocks_one]

theorem doubleMatrix_mul (A B : NaturalSL K r) :
    doubleMatrix K r (A * B) = doubleMatrix K r A * doubleMatrix K r B := by
  unfold doubleMatrix
  rw [_root_.mul_inv_rev]
  change Matrix.fromBlocks (A.val * B.val) 0 0 ((B⁻¹).val * (A⁻¹).val).transpose =
    Matrix.fromBlocks A.val 0 0 (A⁻¹).val.transpose *
      Matrix.fromBlocks B.val 0 0 (B⁻¹).val.transpose
  rw [Matrix.fromBlocks_multiply, Matrix.transpose_mul]
  simp only [mul_zero, zero_mul, add_zero, zero_add]

def doubleUnit (A : NaturalSL K r) : (Mat K r)ˣ where
  val := doubleMatrix K r A
  inv := doubleMatrix K r A⁻¹
  val_inv := by rw [← doubleMatrix_mul, mul_inv_cancel, doubleMatrix_one]
  inv_val := by rw [← doubleMatrix_mul, inv_mul_cancel, doubleMatrix_one]

def doubleHom : NaturalSL K r →* (Mat K r)ˣ where
  toFun := doubleUnit K r
  map_one' := Units.ext (doubleMatrix_one K r)
  map_mul' A B := Units.ext (doubleMatrix_mul K r A B)

def chainMatrix (i j : Fin r) : Mat K r :=
  Matrix.single (Sum.inl i) (Sum.inl j) 1 - Matrix.single (Sum.inr j) (Sum.inr i) 1

theorem doubleHom_elementary_val (i j : Fin r) (hij : i ≠ j) (a : K) :
    ((doubleHom K r (elementary hij a)) : Mat K r) = 1 + a • chainMatrix K r i j := by
  change Matrix.fromBlocks (Matrix.transvection i j a) 0 0
      ((elementary hij a)⁻¹).val.transpose = _
  rw [elementary_inv, elementary_coe]
  ext x y
  cases x <;> cases y <;>
    simp [chainMatrix, Matrix.transvection, Matrix.single_apply,
      Matrix.one_apply, Matrix.fromBlocks, Matrix.smul_apply, Matrix.sub_apply] <;>
      (try split_ifs) <;> ring

theorem adjacent_elementary_mem (i j : Fin r) (hij : i ≠ j)
    (hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val) (a : K) :
    doubleHom K r (elementary hij a) ∈ elementaryRootGroup K r := by
  rcases hadj with hpos | hneg
  · have hi : i.val + 1 < r := by rw [hpos]; exact j.isLt
    have hn : (⟨i.val + 1, hi⟩ : Fin r) = j := Fin.ext hpos
    have he : doubleHom K r (elementary hij a) = rootTransvection K r false i a := by
      apply Units.ext
      rw [doubleHom_elementary_val]
      change 1 + a • chainMatrix K r i j = 1 + a • positive K r i
      rw [positive, dif_pos hi, hn]
      rfl
    rw [he]
    exact rootTransvection_mem K r false i a
  · have hj : j.val + 1 < r := by rw [hneg]; exact i.isLt
    have hn : (⟨j.val + 1, hj⟩ : Fin r) = i := Fin.ext hneg
    have he : doubleHom K r (elementary hij a) = rootTransvection K r true j a := by
      apply Units.ext
      rw [doubleHom_elementary_val]
      change 1 + a • chainMatrix K r i j = 1 + a • negative K r j
      simp only [negative, positive, dif_pos hj, hn, Matrix.transpose_sub,
        Matrix.transpose_single, chainMatrix]
    rw [he]
    exact rootTransvection_mem K r true j a

theorem doubleHom_range_le : (doubleHom K r).range ≤ elementaryRootGroup K r := by
  let H := (elementaryRootGroup K r).comap (doubleHom K r)
  have ht : H = ⊤ := CFSGOrthogonalDGenerationAdjacentSL.eq_top_of_adjacent r H
    (fun i j hij hadj a => adjacent_elementary_mem K r i j hij hadj a)
  rintro _ ⟨A, rfl⟩
  change A ∈ H
  rw [ht]
  trivial

def doubleIntoElementary : NaturalSL K r →* elementaryRootGroup K r :=
  (doubleHom K r).codRestrict (elementaryRootGroup K r)
    (fun A => doubleHom_range_le K r ⟨A, rfl⟩)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSLDouble
