import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMiddleArrays

/-! Exact general upper block arrays before removing their middle block.
The form restriction and factorization are literal identities, enabling
recursive upper-subgroup factorization without a full-unitary theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperArrays
variable {K J : Type*} [CommRing K] [Fintype J] [DecidableEq J]

def upperMiddleArray (w : J → K) (A : Matrix J J K) (v : J → K) (b : K) :
    Matrix (Index J) (Index J) K
  | .inl _, .inl _ => 1
  | .inl _, .inr (.inl j) => w j
  | .inl _, .inr (.inr _) => b
  | .inr (.inl _), .inl _ => 0
  | .inr (.inl i), .inr (.inl j) => A i j
  | .inr (.inl i), .inr (.inr _) => v i
  | .inr (.inr _), .inl _ => 0
  | .inr (.inr _), .inr (.inl _) => 0
  | .inr (.inr _), .inr (.inr _) => 1

theorem upperMiddleArray_one (w v : J → K) (b : K) :
    upperMiddleArray w 1 v b = upperArray w v b := by
  ext (u | (i | u)) (z | (j | z)) <;> simp [upperMiddleArray, upperArray, Matrix.one_apply]

theorem upperArray_mul_middleArray (w v : J → K) (b : K) (A : Matrix J J K) :
    upperArray w v b * middleArray A = upperMiddleArray (w ᵥ* A) A v b := by
  ext (u | (i | u)) (z | (j | z))
  all_goals simp [upperArray, middleArray, upperMiddleArray, Matrix.mul_apply,
    Fintype.sum_sum_type, Matrix.vecMul, dotProduct, ite_mul, mul_ite]

theorem upperMiddleArray_factor (w v : J → K) (b : K) (A : (Matrix J J K)ˣ) :
    upperMiddleArray w (A : Matrix J J K) v b =
      upperArray (w ᵥ* ((A⁻¹ : (Matrix J J K)ˣ) : Matrix J J K)) v b * middleArray (A : Matrix J J K) := by
  rw [upperArray_mul_middleArray, Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]

theorem upperMiddleArray_isometry_middle (f : K →+* K) (eps : K)
    (H A : Matrix J J K) (w v : J → K) (b : K)
    (h : ((upperMiddleArray w A v b).map f).transpose * blockForm eps H *
      upperMiddleArray w A v b = blockForm eps H) :
    (A.map f).transpose * H * A = H := by
  ext i j
  have he := congrArg (fun M : Matrix (Index J) (Index J) K =>
    M (.inr (.inl i)) (.inr (.inl j))) h
  dsimp only at he
  simpa [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Fintype.sum_sum_type, blockForm, upperMiddleArray] using he

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperArrays
