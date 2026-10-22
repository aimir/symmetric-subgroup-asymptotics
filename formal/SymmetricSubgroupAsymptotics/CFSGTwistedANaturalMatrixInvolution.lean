import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
import SymmetricSubgroupAsymptotics.CFSGAlgebraConjugationAction
import Mathlib.Tactic.NoncommRing

/-! Explicit target-side maps for diagram reversal. The negative transpose
is a genuine Lie homomorphism, and the signed reversal is an actual matrix
unit over every commutative ring. No source or unitary identification is
built into these definitions. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
variable (R : Type*) [CommRing R] (r : ℕ)

def negativeTranspose : Mat R r →ₗ⁅R⁆ Mat R r where
  toFun X := -X.transpose
  map_add' X Y := by simp only [Matrix.transpose_add, neg_add]
  map_smul' t X := by simp only [Matrix.transpose_smul, smul_neg, RingHom.id_apply]
  map_lie' {X} {Y} := by
    simp only [Ring.lie_def, Matrix.transpose_sub, Matrix.transpose_mul,
      neg_sub, neg_mul, mul_neg, neg_neg]

@[simp] theorem negativeTranspose_apply (X : Mat R r) :
    negativeTranspose R r X = -X.transpose := rfl

theorem negativeTranspose_involutive : Function.Involutive (negativeTranspose R r) := by
  intro X
  simp only [negativeTranspose_apply, Matrix.transpose_neg, Matrix.transpose_transpose, neg_neg]

theorem unitConjugation_mul (u : (Mat R r)ˣ) (X Y : Mat R r) :
    ((u : Mat R r) * X * (↑(u⁻¹) : Mat R r)) *
      ((u : Mat R r) * Y * (↑(u⁻¹) : Mat R r)) =
      (u : Mat R r) * (X * Y) * (↑(u⁻¹) : Mat R r) := by
  calc
    _ = (u : Mat R r) * X * ((↑(u⁻¹) : Mat R r) * (u : Mat R r)) *
        Y * (↑(u⁻¹) : Mat R r) := by noncomm_ring
    _ = _ := by rw [Units.inv_mul]; simp only [mul_one, mul_assoc]

def unitConjugationLie (u : (Mat R r)ˣ) : Mat R r →ₗ⁅R⁆ Mat R r where
  __ := (CFSGAlgebraConjugationAction.action R (Mat R r) u).toLinearMap
  map_lie' {X} {Y} := by
    change (u : Mat R r) * (X * Y - Y * X) * (↑(u⁻¹) : Mat R r) =
      ((u : Mat R r) * X * (↑(u⁻¹) : Mat R r)) *
        ((u : Mat R r) * Y * (↑(u⁻¹) : Mat R r)) -
      ((u : Mat R r) * Y * (↑(u⁻¹) : Mat R r)) *
        ((u : Mat R r) * X * (↑(u⁻¹) : Mat R r))
    rw [unitConjugation_mul, unitConjugation_mul]
    simp only [mul_sub, sub_mul]

def permutationUnit {I : Type*} [Fintype I] [DecidableEq I]
    (p : Equiv.Perm I) : (Matrix I I R)ˣ where
  val := (1 : Matrix I I R).submatrix p id
  inv := (1 : Matrix I I R).submatrix p.symm id
  val_inv := by
    rw [Matrix.mul_submatrix_one p.symm id]
    simpa only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp,
      Equiv.symm_symm] using Matrix.submatrix_one_equiv p
  inv_val := by
    rw [Matrix.mul_submatrix_one p id]
    simpa only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp] using
      Matrix.submatrix_one_equiv p.symm

def signWeight (i : Fin (r + 1)) : R := (-1 : R) ^ i.val

theorem signWeight_square (i : Fin (r + 1)) :
    signWeight R r i * signWeight R r i = 1 := by
  dsimp only [signWeight]
  rw [← mul_pow]
  simp only [neg_one_mul, neg_neg, one_pow]

def signDiagonalUnit : (Mat R r)ˣ where
  val := Matrix.diagonal (signWeight R r)
  inv := Matrix.diagonal (signWeight R r)
  val_inv := by simp only [Matrix.diagonal_mul_diagonal, signWeight_square, Matrix.diagonal_one]
  inv_val := by simp only [Matrix.diagonal_mul_diagonal, signWeight_square, Matrix.diagonal_one]

def signedReversalUnit : (Mat R r)ˣ :=
  signDiagonalUnit R r * permutationUnit R (Fin.revPerm : Equiv.Perm (Fin (r + 1)))

theorem signedReversalUnit_val :
    (signedReversalUnit R r : Mat R r) =
      Matrix.diagonal (signWeight R r) *
        (1 : Mat R r).submatrix (Fin.revPerm : Equiv.Perm (Fin (r + 1))) id := rfl

def matrixDiagram : Mat R r →ₗ⁅R⁆ Mat R r :=
  (unitConjugationLie R r (signedReversalUnit R r)).comp (negativeTranspose R r)

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
