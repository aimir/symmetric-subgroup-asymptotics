import SymmetricSubgroupAsymptotics.CFSGSymplecticPositiveSerreSupport
import SymmetricSubgroupAsymptotics.CFSGSquareZeroAdjoint

/-! The two remaining Serre-power identities hold for the actual
symplectic matrices in every rank. Only target-side square-zero and support
identities are used; no injectivity of the source Serre quotient is used. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
variable (R : Type*) [CommRing R] (r : ℕ)

theorem B_offdiag_cases (i j : Fin r) (hij : i ≠ j) :
    CartanMatrix.B r i j = 0 ∨ CartanMatrix.B r i j = -1 ∨ CartanMatrix.B r i j = -2 := by
  by_cases hf : i.val + 1 = j.val
  · by_cases hl : j.val = r - 1
    · exact Or.inr (Or.inr (by simp [CartanMatrix.B, hij, hf, hl]))
    · exact Or.inr (Or.inl (by simp [CartanMatrix.B, hij, hf, hl]))
  · by_cases hr : j.val + 1 = i.val
    · exact Or.inr (Or.inl (by simp [CartanMatrix.B, hij, hf, hr]))
    · exact Or.inl (by simp [CartanMatrix.B, hij, hf, hr])

theorem positive_serre (i j : Fin r) :
    (LieAlgebra.ad R (Mat R r) (positive R r i) ^ (-CartanMatrix.B r i j).toNat)
      ⁅positive R r i, positive R r j⁆ = 0 := by
  by_cases hij : i = j
  · subst j
    rw [lie_self]
    exact map_zero _
  · have he : positive R r i * positive R r i = 0 := by
      simpa only [pow_two] using positive_sq_zero R r i
    rcases B_offdiag_cases r i j hij with hc | hc | hc
    · rw [hc]
      change ⁅positive R r i, positive R r j⁆ = 0
      exact positive_lie_of_cartan_zero R r i j hc
    · rw [hc]
      change ⁅positive R r i, ⁅positive R r i, positive R r j⁆⁆ = 0
      rw [CFSGSquareZeroAdjoint.lie_lie _ _ he]
      have hn : CartanMatrix.B r i j ≠ -2 := by omega
      simp only [positive_sandwich_of_not_neg_two R r i j hn, add_zero, neg_zero]
    · rw [hc]
      change ⁅positive R r i, ⁅positive R r i, ⁅positive R r i, positive R r j⁆⁆⁆ = 0
      exact CFSGSquareZeroAdjoint.lie_lie_lie _ _ he

theorem transpose_lie (X Y : Mat R r) : ⁅X, Y⁆.transpose = -⁅X.transpose, Y.transpose⁆ := by
  simp only [Ring.lie_def, Matrix.transpose_sub, Matrix.transpose_mul, neg_sub]

theorem negative_lie_of_cartan_zero (i j : Fin r) (hzero : CartanMatrix.B r i j = 0) :
    ⁅negative R r i, negative R r j⁆ = 0 := by
  have h := congrArg Matrix.transpose (positive_lie_of_cartan_zero R r i j hzero)
  rw [transpose_lie, Matrix.transpose_zero] at h
  exact neg_eq_zero.mp h

theorem negative_sandwich_of_not_neg_two (i j : Fin r)
    (hij : CartanMatrix.B r i j ≠ -2) :
    negative R r i * negative R r j * negative R r i = 0 := by
  have h := congrArg Matrix.transpose (positive_sandwich_of_not_neg_two R r i j hij)
  simpa only [negative, Matrix.transpose_mul, Matrix.transpose_zero, mul_assoc] using h

theorem negative_serre (i j : Fin r) :
    (LieAlgebra.ad R (Mat R r) (negative R r i) ^ (-CartanMatrix.B r i j).toNat)
      ⁅negative R r i, negative R r j⁆ = 0 := by
  by_cases hij : i = j
  · subst j
    rw [lie_self]
    exact map_zero _
  · have he : negative R r i * negative R r i = 0 := by
      simpa only [pow_two] using negative_sq_zero R r i
    rcases B_offdiag_cases r i j hij with hc | hc | hc
    · rw [hc]
      change ⁅negative R r i, negative R r j⁆ = 0
      exact negative_lie_of_cartan_zero R r i j hc
    · rw [hc]
      change ⁅negative R r i, ⁅negative R r i, negative R r j⁆⁆ = 0
      rw [CFSGSquareZeroAdjoint.lie_lie _ _ he]
      have hn : CartanMatrix.B r i j ≠ -2 := by omega
      simp only [negative_sandwich_of_not_neg_two R r i j hn, add_zero, neg_zero]
    · rw [hc]
      change ⁅negative R r i, ⁅negative R r i, ⁅negative R r i, negative R r j⁆⁆⁆ = 0
      exact CFSGSquareZeroAdjoint.lie_lie_lie _ _ he

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
