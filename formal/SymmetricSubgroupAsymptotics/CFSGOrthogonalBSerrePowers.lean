import SymmetricSubgroupAsymptotics.CFSGOrthogonalBMatrixOpposition
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPositiveCommutation
import SymmetricSubgroupAsymptotics.CFSGCubicRootAdjoint

/-! Actual Serre adjoint powers, with the short-root cube-zero case
handled separately from the long-root square-zero case. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
variable (R : Type*) [CommRing R] (r : ℕ)

private theorem cartan_off_diagonal (i j : Fin r) (hij : i≠j) :
    CartanMatrix.C r i j=0 ∨ CartanMatrix.C r i j= -1 ∨ CartanMatrix.C r i j= -2 := by
  simp only [CartanMatrix.C,Matrix.of_apply,if_neg hij]
  split_ifs <;> omega

private theorem chain_of_cartan_neg_one (i j : Fin r) (hij : CartanMatrix.C r i j= -1) :
    i.val+1<r := by
  by_contra hi
  have hil := i.isLt
  have hjl := j.isLt
  simp only [CartanMatrix.C,Matrix.of_apply] at hij
  split_ifs at hij <;> omega

theorem negative_lie_of_cartan_zero (i j : Fin r) (hz : CartanMatrix.C r i j=0) :
    ⁅negative R r i,negative R r j⁆=0 := by
  have hh := congrArg (opposition R r) (positive_lie_of_cartan_zero R r i j hz)
  simpa only [Ring.lie_def,map_sub,map_mul,opposition_positive,map_zero,
    neg_mul,mul_neg,neg_neg] using hh

theorem positive_serre (i j : Fin r) :
    (LieAlgebra.ad R (Mat R r) (positive R r i)^(-CartanMatrix.C r i j).toNat)
      ⁅positive R r i,positive R r j⁆=0 := by
  by_cases hij : i=j
  · subst j
    rw [lie_self,map_zero]
  · rcases cartan_off_diagonal r i j hij with hz|hz|hz
    · rw [hz]
      simpa only [neg_zero,Int.toNat_zero,pow_zero,Module.End.one_apply] using
        positive_lie_of_cartan_zero R r i j hz
    · have hi := chain_of_cartan_neg_one r i j hz
      have he : positive R r i*positive R r i=0 := by
        rw [positive_square]
        simp only [positiveSecond,if_pos hi,add_zero]
      rw [hz]
      change ⁅positive R r i,⁅positive R r i,positive R r j⁆⁆=0
      rw [CFSGSquareZeroAdjoint.lie_lie _ _ he,positive_sandwich]
      simp only [zero_add,neg_zero]
    · rw [hz]
      change ⁅positive R r i,⁅positive R r i,⁅positive R r i,positive R r j⁆⁆⁆=0
      exact CFSGCubicRootAdjoint.lie_lie_lie _ _ (positive_cube R r i) (positive_sandwich R r i j)

theorem negative_serre (i j : Fin r) :
    (LieAlgebra.ad R (Mat R r) (negative R r i)^(-CartanMatrix.C r i j).toNat)
      ⁅negative R r i,negative R r j⁆=0 := by
  by_cases hij : i=j
  · subst j
    rw [lie_self,map_zero]
  · rcases cartan_off_diagonal r i j hij with hz|hz|hz
    · rw [hz]
      simpa only [neg_zero,Int.toNat_zero,pow_zero,Module.End.one_apply] using
        negative_lie_of_cartan_zero R r i j hz
    · have hi := chain_of_cartan_neg_one r i j hz
      have he : negative R r i*negative R r i=0 := by
        rw [negative_square]
        simp only [negativeSecond,if_pos hi,add_zero]
      rw [hz]
      change ⁅negative R r i,⁅negative R r i,negative R r j⁆⁆=0
      rw [CFSGSquareZeroAdjoint.lie_lie _ _ he,negative_sandwich]
      simp only [zero_add,neg_zero]
    · rw [hz]
      change ⁅negative R r i,⁅negative R r i,⁅negative R r i,negative R r j⁆⁆⁆=0
      exact CFSGCubicRootAdjoint.lie_lie_lie _ _ (negative_cube R r i) (negative_sandwich R r i j)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
