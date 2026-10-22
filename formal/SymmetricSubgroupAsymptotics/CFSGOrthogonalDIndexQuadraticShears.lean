import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticForm
import SymmetricSubgroupAsymptotics.CFSGMatrixShearUnits

/-! Split-quadratic preservation forces every diagonal of an upper
shear to vanish, also in characteristic two. Thus the spurious single
E(pos_i,neg_i) direction of the polar-form centralizer is excluded from
the actual D group by a direct original-coordinate calculation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticShears
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexQuadraticForm CFSGMatrixShearUnits
variable (K : Type) [Field K]

def rightVector {r : ℕ} (y : Fin r → K) : Index r → K := Sum.elim 0 y

theorem splitQ_rightVector {r : ℕ} (y : Fin r → K) : splitQ K (rightVector K y) = 0 := by
  simp [splitQ, leftPart, rightPart, rightVector]

theorem splitQ_upper_rightVector {r : ℕ} (S : Matrix (Fin r) (Fin r) K) (y : Fin r → K) :
    splitQ K ((upper S : Mat K r) *ᵥ rightVector K y) = (S *ᵥ y) ⬝ᵥ y := by
  simp [splitQ, leftPart, rightPart, rightVector, upper, Matrix.fromBlocks_mulVec,
    Function.comp_def]

theorem upper_diagonal_zero_of_preserves_splitQ {r : ℕ} (S : Matrix (Fin r) (Fin r) K)
    (hS : ∀ x : Index r → K, splitQ K ((upper S : Mat K r) *ᵥ x) = splitQ K x) (i : Fin r) :
    S i i = 0 := by
  have h := hS (rightVector K (Pi.single i 1))
  rw [splitQ_upper_rightVector, splitQ_rightVector] at h
  simpa only [Matrix.mulVec_single_one, dotProduct_single_one, Matrix.col_apply] using h

theorem upper_pair_sum_zero_of_preserves_splitQ {r : ℕ} (S : Matrix (Fin r) (Fin r) K)
    (hS : ∀ x : Index r → K, splitQ K ((upper S : Mat K r) *ᵥ x) = splitQ K x) (i j : Fin r) :
    S i j + S j i = 0 := by
  have h := hS (rightVector K (Pi.single i 1 + Pi.single j 1))
  rw [splitQ_upper_rightVector, splitQ_rightVector] at h
  have hi := upper_diagonal_zero_of_preserves_splitQ K S hS i
  have hj := upper_diagonal_zero_of_preserves_splitQ K S hS j
  simpa only [Matrix.mulVec_add, add_dotProduct, dotProduct_add, Matrix.mulVec_single_one,
    dotProduct_single_one, Pi.add_apply, Matrix.col_apply, hi, hj, zero_add, add_zero, add_comm] using h

theorem upper_single_diagonal_mem_implies_zero (s : ℕ) (i : Fin (s + 4)) (a : K)
    (ha : upper (Matrix.single i i a) ∈ elementaryRootGroup K (s + 4)) : a = 0 := by
  have h := upper_diagonal_zero_of_preserves_splitQ K (Matrix.single i i a)
    (elementary_preserves_splitQ K s ⟨upper (Matrix.single i i a), ha⟩) i
  simpa [Matrix.single_apply] using h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticShears
