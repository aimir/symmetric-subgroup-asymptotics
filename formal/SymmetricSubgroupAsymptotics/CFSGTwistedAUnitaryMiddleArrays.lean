import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperIsometry

/-! Literal block embedding diag(1,A,1), with its exact determinant and
signed-form equation. These are symbolic array identities over the actual
middle index, not an assumed unitary subgroup embedding. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperArrays
variable {K J : Type*} [CommRing K] [Fintype J] [DecidableEq J]

def middleArray (A : Matrix J J K) : Matrix (Index J) (Index J) K
  | .inl _, .inl _ => 1
  | .inr (.inl i), .inr (.inl j) => A i j
  | .inr (.inr _), .inr (.inr _) => 1
  | _, _ => 0

theorem middleArray_one : middleArray (1 : Matrix J J K) = 1 := by
  ext (u | (i | u)) (v | (j | v)) <;> simp [middleArray, Matrix.one_apply]

theorem middleArray_mul (A B : Matrix J J K) :
    middleArray (A * B) = middleArray A * middleArray B := by
  ext (u | (i | u)) (v | (j | v))
  all_goals simp [middleArray, Matrix.mul_apply, Fintype.sum_sum_type]

def middleUnit (A : (Matrix J J K)ˣ) : (Matrix (Index J) (Index J) K)ˣ where
  val := middleArray (A : Matrix J J K)
  inv := middleArray ((A⁻¹ : (Matrix J J K)ˣ) : Matrix J J K)
  val_inv := by rw [← middleArray_mul, Units.mul_inv, middleArray_one]
  inv_val := by rw [← middleArray_mul, Units.inv_mul, middleArray_one]

def middleUnitHom : (Matrix J J K)ˣ →* (Matrix (Index J) (Index J) K)ˣ where
  toFun := middleUnit
  map_one' := by apply Units.ext; exact middleArray_one
  map_mul' A B := by apply Units.ext; exact middleArray_mul _ _

theorem middleUnitHom_injective : Function.Injective (middleUnitHom (K := K) (J := J)) := by
  intro A B he
  apply Units.ext
  ext i j
  exact congrArg (fun u : (Matrix (Index J) (Index J) K)ˣ =>
    (u : Matrix (Index J) (Index J) K) (.inr (.inl i)) (.inr (.inl j))) he

theorem middleArray_det (A : Matrix J J K) : (middleArray A).det = A.det := by
  have he : middleArray A = Matrix.fromBlocks (1 : Matrix Unit Unit K) 0 0
      (Matrix.fromBlocks A 0 0 (1 : Matrix Unit Unit K)) := by
    ext (u | (i | u)) (v | (j | v)) <;> simp [middleArray, Matrix.one_apply]
  rw [he, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem middleArray_map_transpose (f : K →+* K) (A : Matrix J J K) :
    ((middleArray A).map f).transpose = middleArray ((A.map f).transpose) := by
  ext (u | (i | u)) (v | (j | v))
  all_goals simp [middleArray, Matrix.transpose_apply, Matrix.map_apply]

theorem middleArray_mul_blockForm (B H : Matrix J J K) (eps : K) :
    middleArray B * blockForm eps H = blockForm eps (B * H) := by
  ext (u | (i | u)) (v | (j | v))
  all_goals simp [middleArray, blockForm, Matrix.mul_apply, Fintype.sum_sum_type]

theorem blockForm_mul_middleArray (H A : Matrix J J K) (eps : K) :
    blockForm eps H * middleArray A = blockForm eps (H * A) := by
  ext (u | (i | u)) (v | (j | v))
  all_goals simp [middleArray, blockForm, Matrix.mul_apply, Fintype.sum_sum_type]

theorem middleArray_isometry (f : K →+* K) (eps : K) (H A : Matrix J J K)
    (hA : (A.map f).transpose * H * A = H) :
    ((middleArray A).map f).transpose * blockForm eps H * middleArray A = blockForm eps H := by
  rw [middleArray_map_transpose, middleArray_mul_blockForm, blockForm_mul_middleArray, hA]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperArrays
