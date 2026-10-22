import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryParameters
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block

/-! Literal three-block upper arrays for the hyperbolic-pair radical.
Multiplication, inverse and determinant are symbolic in the entire middle
index type. These are matrix identities, not a stipulated unitary-group
presentation or an assertion that the original fixed group is derived. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperArrays
variable {K J : Type*} [CommRing K] [Fintype J] [DecidableEq J]

abbrev Index (J : Type*) := Unit ⊕ (J ⊕ Unit)

def upperArray (w v : J → K) (b : K) : Matrix (Index J) (Index J) K
  | .inl _, .inl _ => 1
  | .inl _, .inr (.inl j) => w j
  | .inl _, .inr (.inr _) => b
  | .inr (.inl _), .inl _ => 0
  | .inr (.inl i), .inr (.inl j) => if i = j then 1 else 0
  | .inr (.inl i), .inr (.inr _) => v i
  | .inr (.inr _), .inl _ => 0
  | .inr (.inr _), .inr (.inl _) => 0
  | .inr (.inr _), .inr (.inr _) => 1

theorem upperArray_zero : upperArray (0 : J → K) 0 0 = 1 := by
  ext (i | (i | i)) (j | (j | j)) <;> simp [upperArray, Matrix.one_apply]

theorem upperArray_mul (w v w' v' : J → K) (b b' : K) :
    upperArray w v b * upperArray w' v' b' =
      upperArray (w + w') (v + v') (b + b' + dotProduct w v') := by
  ext (i | (i | i)) (j | (j | j))
  all_goals simp [upperArray, Matrix.mul_apply, Fintype.sum_sum_type, dotProduct,
    ite_mul, mul_ite, add_comm, add_left_comm, add_assoc]

theorem upperArray_inverse_right (w v : J → K) (b : K) :
    upperArray w v b * upperArray (-w) (-v) (-b + dotProduct w v) = 1 := by
  rw [upperArray_mul]
  have hc : b + (-b + dotProduct w v) + dotProduct w (-v) = 0 := by
    rw [dotProduct_neg]
    ring
  simp only [add_neg_cancel, hc, upperArray_zero]

theorem upperArray_inverse_left (w v : J → K) (b : K) :
    upperArray (-w) (-v) (-b + dotProduct w v) * upperArray w v b = 1 := by
  rw [upperArray_mul]
  have hc : (-b + dotProduct w v) + b + dotProduct (-w) v = 0 := by
    rw [neg_dotProduct]
    ring
  simp only [neg_add_cancel, hc, upperArray_zero]

def upperUnit (w v : J → K) (b : K) : (Matrix (Index J) (Index J) K)ˣ where
  val := upperArray w v b
  inv := upperArray (-w) (-v) (-b + dotProduct w v)
  val_inv := upperArray_inverse_right w v b
  inv_val := upperArray_inverse_left w v b

theorem upperArray_fromBlocks (w v : J → K) (b : K) :
    upperArray w v b = Matrix.fromBlocks (1 : Matrix Unit Unit K)
      (fun _ j => match j with | .inl j => w j | .inr _ => b) 0
      (Matrix.fromBlocks (1 : Matrix J J K) (fun i (_ : Unit) => v i) 0
        (1 : Matrix Unit Unit K)) := by
  ext (i | (i | i)) (j | (j | j)) <;> simp [upperArray, Matrix.one_apply]

theorem upperArray_det (w v : J → K) (b : K) : Matrix.det (upperArray w v b) = 1 := by
  rw [upperArray_fromBlocks, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_fromBlocks_zero₂₁]
  simp

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperArrays
