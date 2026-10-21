import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices

/-! Basis propagation for the original natural type-B root matrices.
The terminal short root has its genuine factors two and minus one. -/
set_option autoImplicit false
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
variable (R : Type*) [CommRing R]

theorem positive_castSucc_basis (r : ℕ) (i : Fin r) :
    positive R (r + 1) i.castSucc *ᵥ Pi.single (pos (r + 1) i.succ) 1 =
      Pi.single (pos (r + 1) i.castSucc) 1 := by
  rw [Matrix.mulVec_single_one]
  funext x
  simp [positive, pos, neg, Matrix.col, Matrix.single, Pi.single_apply,
    Fin.succ, eq_comm]

theorem negative_castSucc_basis (r : ℕ) (i : Fin r) :
    negative R (r + 1) i.castSucc *ᵥ Pi.single (neg (r + 1) i.succ) 1 =
      -Pi.single (neg (r + 1) i.castSucc) 1 := by
  rw [Matrix.mulVec_single_one]
  funext x
  simp [negative, pos, neg, Matrix.col, Matrix.single, Pi.single_apply,
    Fin.succ, eq_comm]

theorem negative_last_positive_basis (r : ℕ) :
    negative R (r + 1) (Fin.last r) *ᵥ Pi.single (pos (r + 1) (Fin.last r)) 1 =
      (2 : R) • Pi.single (middle (r + 1)) 1 := by
  rw [Matrix.mulVec_single_one]
  funext x
  simp [negative, pos, neg, middle, Matrix.col, Matrix.single, Pi.single_apply, eq_comm]

theorem negative_last_middle_basis (r : ℕ) :
    negative R (r + 1) (Fin.last r) *ᵥ Pi.single (middle (r + 1)) 1 =
      -Pi.single (neg (r + 1) (Fin.last r)) 1 := by
  rw [Matrix.mulVec_single_one]
  funext x
  simp [negative, pos, neg, middle, Matrix.col, Matrix.single, Pi.single_apply, eq_comm]

theorem terminal_square_product (r : ℕ) :
    (positive R (r + 1) (Fin.last r) * positive R (r + 1) (Fin.last r)) *
      (negative R (r + 1) (Fin.last r) * negative R (r + 1) (Fin.last r)) =
        Matrix.single (pos (r + 1) (Fin.last r)) (pos (r + 1) (Fin.last r)) 4 := by
  rw [positive_square, negative_square]
  simp [positiveSecond, negativeSecond, mul_add, pos, neg,
    ← Matrix.single_add] <;> norm_num

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
