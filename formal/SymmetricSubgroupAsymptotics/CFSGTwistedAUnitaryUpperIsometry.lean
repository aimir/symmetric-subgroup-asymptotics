import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperArrays

/-! The actual three-block form calculation for upper radical arrays.
The hypotheses are the three displayed scalar cross-term equations;
subsequent parameter construction will discharge them on the literal
quadratic extension. No group/model recognition enters this identity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperArrays
variable {K J : Type*} [CommRing K] [Fintype J] [DecidableEq J]

def blockForm (eps : K) (H : Matrix J J K) : Matrix (Index J) (Index J) K
  | .inl _, .inl _ => 0
  | .inl _, .inr (.inl _) => 0
  | .inl _, .inr (.inr _) => 1
  | .inr (.inl _), .inl _ => 0
  | .inr (.inl i), .inr (.inl j) => H i j
  | .inr (.inl _), .inr (.inr _) => 0
  | .inr (.inr _), .inl _ => eps
  | .inr (.inr _), .inr (.inl _) => 0
  | .inr (.inr _), .inr (.inr _) => 0

def formTimesUpper (eps : K) (H : Matrix J J K) (w v : J → K) (b : K) :
    Matrix (Index J) (Index J) K
  | .inl _, .inl _ => 0
  | .inl _, .inr (.inl _) => 0
  | .inl _, .inr (.inr _) => 1
  | .inr (.inl _), .inl _ => 0
  | .inr (.inl i), .inr (.inl j) => H i j
  | .inr (.inl i), .inr (.inr _) => (H *ᵥ v) i
  | .inr (.inr _), .inl _ => eps
  | .inr (.inr _), .inr (.inl j) => eps * w j
  | .inr (.inr _), .inr (.inr _) => eps * b

theorem blockForm_mul_upper (eps : K) (H : Matrix J J K) (w v : J → K) (b : K) :
    blockForm eps H * upperArray w v b = formTimesUpper eps H w v b := by
  ext (i | (i | i)) (j | (j | j))
  all_goals simp [blockForm, upperArray, formTimesUpper, Matrix.mul_apply,
    Fintype.sum_sum_type, Matrix.mulVec, dotProduct, ite_mul, mul_ite]

theorem upperArray_isometry (sigma : K →+* K) (eps : K) (H : Matrix J J K)
    (w v : J → K) (b : K)
    (hleft : ∀ i, sigma (w i) + (H *ᵥ v) i = 0)
    (hright : ∀ j, ((sigma ∘ v) ᵥ* H) j + eps * w j = 0)
    (hcentral : sigma b + dotProduct (sigma ∘ v) (H *ᵥ v) + eps * b = 0) :
    ((upperArray w v b).map sigma).transpose * blockForm eps H * upperArray w v b =
      blockForm eps H := by
  rw [mul_assoc, blockForm_mul_upper]
  ext (i | (i | i)) (j | (j | j))
  all_goals simp_all [upperArray, formTimesUpper, blockForm, Matrix.mul_apply,
    Fintype.sum_sum_type, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.mulVec, Matrix.vecMul, dotProduct, Function.comp_apply, apply_ite,
    ite_mul, mul_ite, add_assoc, add_left_comm, add_comm]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperArrays
