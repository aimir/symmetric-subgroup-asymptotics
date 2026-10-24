import SymmetricSubgroupAsymptotics.CFSGSymplecticPointTailCoordinates
import Mathlib.Tactic.Ring

/-! The literal tail and partner column of a first-vector stabilizer
obey the natural affine multiplication law. The partner is not assumed
fixed. These identities work over every field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticPointAffineCoordinates
open CFSGSymplecticSerreMatrices CFSGSymplecticStabilizerCoordinates
open CFSGSymplecticPointTailCoordinates
variable (K : Type) [Field K]

theorem tailMatrix_mul_of_fixed_first (r : ℕ) (A B : Mat K (r+1))
    (heA : FixesFirstVector K r A)
    (hB : PreservesPairing (r+1) B) (heB : FixesFirstVector K r B) :
    tailMatrix r (A*B) = tailMatrix r A * tailMatrix r B := by
  ext i j
  have hp : A (tailIndex r i) (Sum.inl 0) = 0 := by
    have h := fixed_basis_column (r+1) A (Sum.inl 0) heA (tailIndex r i)
    cases i <;> simpa [tailIndex, Pi.single_apply] using h
  have hn : B (Sum.inr 0) (tailIndex r j) = 0 := by
    have h := fixed_positive_basis_row (r+1) B hB 0 heB (tailIndex r j)
    cases j <;> simpa [tailIndex, Pi.single_apply] using h
  simp only [tailIndex] at hp hn
  simp only [tailMatrix, Matrix.submatrix_apply, Matrix.mul_apply,
    Fintype.sum_sum_type, Fin.sum_univ_succ, tailIndex, Sum.map_inl, Sum.map_inr,
    hp, hn, zero_mul, mul_zero, zero_add, add_zero]

def partnerColumn (r : ℕ) (A : Mat K (r+1)) : Index r → K :=
  fun i => A (tailIndex r i) (Sum.inr 0)

theorem partnerColumn_mul (r : ℕ) (A B : Mat K (r+1))
    (heA : FixesFirstVector K r A)
    (hB : PreservesPairing (r+1) B) (heB : FixesFirstVector K r B) :
    partnerColumn K r (A*B) =
      partnerColumn K r A + tailMatrix r A *ᵥ partnerColumn K r B := by
  funext i
  have hp : A (tailIndex r i) (Sum.inl 0) = 0 := by
    have h := fixed_basis_column (r+1) A (Sum.inl 0) heA (tailIndex r i)
    cases i <;> simpa [tailIndex, Pi.single_apply] using h
  have hn : B (Sum.inr 0) (Sum.inr 0) = 1 := by
    have h := fixed_positive_basis_row (r+1) B hB 0 heB (Sum.inr 0)
    simpa only [Pi.single_eq_same] using h
  simp only [tailIndex] at hp
  simp only [partnerColumn, tailMatrix, Matrix.submatrix_apply, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Pi.add_apply, Fintype.sum_sum_type,
    Fin.sum_univ_succ, tailIndex, Sum.map_inl, Sum.map_inr,
    hp, hn, zero_mul, mul_one, zero_add]
  ring

end SymmetricSubgroupAsymptotics.CFSGSymplecticPointAffineCoordinates
