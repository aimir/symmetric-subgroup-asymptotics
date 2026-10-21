import SymmetricSubgroupAsymptotics.CFSGOrthogonalDPositiveCommutation
import SymmetricSubgroupAsymptotics.CFSGSquareZeroAdjoint

/-! The two Serre-power families for the original simply laced D table. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
variable (R : Type*) [CommRing R] (r : ℕ)

theorem D_offdiag_cases (i j : Fin r) (hij : i≠j) :
    CartanMatrix.D r i j=0 ∨ CartanMatrix.D r i j=-1 := by
  simp only [CartanMatrix.D,Matrix.of_apply,if_neg hij]
  split_ifs <;> simp

theorem positive_serre (hr : 4≤r) (i j : Fin r) :
    (LieAlgebra.ad R (Mat R r) (positive R r i)^(-CartanMatrix.D r i j).toNat)
      ⁅positive R r i,positive R r j⁆=0 := by
  by_cases hij : i=j
  · subst j
    rw [lie_self]
    exact map_zero _
  · rcases D_offdiag_cases r i j hij with hc | hc
    · rw [hc]
      change ⁅positive R r i,positive R r j⁆=0
      exact positive_lie_of_cartan_zero R r hr i j hc
    · rw [hc]
      change ⁅positive R r i,⁅positive R r i,positive R r j⁆⁆=0
      have he : positive R r i*positive R r i=0 := by simpa only [pow_two] using positive_sq_zero R r i
      rw [CFSGSquareZeroAdjoint.lie_lie _ _ he]
      simp only [positive_sandwich,add_zero,neg_zero]

theorem transpose_lie (X Y : Mat R r) : ⁅X,Y⁆.transpose=-⁅X.transpose,Y.transpose⁆ := by
  simp only [Ring.lie_def,Matrix.transpose_sub,Matrix.transpose_mul,neg_sub]

theorem negative_lie_of_cartan_zero (hr : 4≤r) (i j : Fin r) (hz : CartanMatrix.D r i j=0) :
    ⁅negative R r i,negative R r j⁆=0 := by
  have hh := congrArg Matrix.transpose (positive_lie_of_cartan_zero R r hr i j hz)
  rw [transpose_lie,Matrix.transpose_zero] at hh
  exact neg_eq_zero.mp hh

theorem negative_sandwich (i j : Fin r) : negative R r i*negative R r j*negative R r i=0 := by
  have hh := congrArg Matrix.transpose (positive_sandwich R r i j)
  simpa only [negative,Matrix.transpose_mul,Matrix.transpose_zero,mul_assoc] using hh

theorem negative_serre (hr : 4≤r) (i j : Fin r) :
    (LieAlgebra.ad R (Mat R r) (negative R r i)^(-CartanMatrix.D r i j).toNat)
      ⁅negative R r i,negative R r j⁆=0 := by
  by_cases hij : i=j
  · subst j
    rw [lie_self]
    exact map_zero _
  · rcases D_offdiag_cases r i j hij with hc | hc
    · rw [hc]
      change ⁅negative R r i,negative R r j⁆=0
      exact negative_lie_of_cartan_zero R r hr i j hc
    · rw [hc]
      change ⁅negative R r i,⁅negative R r i,negative R r j⁆⁆=0
      have he : negative R r i*negative R r i=0 := by simpa only [pow_two] using negative_sq_zero R r i
      rw [CFSGSquareZeroAdjoint.lie_lie _ _ he]
      simp only [negative_sandwich,add_zero,neg_zero]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
