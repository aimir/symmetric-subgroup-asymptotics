import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
import SymmetricSubgroupAsymptotics.CFSGIntegralQuadraticRootOperators

/-! Literal natural B root matrices and source-parent arithmetic, uniformly
in the rank and coefficient ring. These are matrix identities only: no
source realization faithfulness is inferred from them. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBUniformRootMatrixArithmetic
open CFSGOrthogonalBSerreMatrices
variable (R : Type*) [CommRing R] (r : ℕ)

def difference (i j : Fin r) : Mat R r :=
  Matrix.single (pos r i) (pos r j) 1 - Matrix.single (neg r j) (neg r i) 1

def short (i : Fin r) : Mat R r :=
  Matrix.single (pos r i) (middle r) 1 - Matrix.single (middle r) (neg r i) 2

def sumRoot (i j : Fin r) : Mat R r :=
  Matrix.single (pos r i) (neg r j) 1 - Matrix.single (pos r j) (neg r i) 1

theorem difference_parent (i j : Fin r) (hi : i.val + 1 < r)
    (hij : i.val + 1 < j.val) :
    ⁅positive R r i, difference R r ⟨i.val + 1, hi⟩ j⁆ = difference R r i j := by
  have hn : (⟨i.val + 1, hi⟩ : Fin r) ≠ i := by
    intro h
    have hv := congrArg Fin.val h
    change i.val + 1 = i.val at hv
    omega
  have hji : j ≠ i := by intro h; subst j; omega
  have hjn : j ≠ (⟨i.val + 1, hi⟩ : Fin r) := by
    intro h
    have hv := congrArg Fin.val h
    change j.val = i.val + 1 at hv
    omega
  simp [positive, hi, difference, Ring.lie_def, sub_mul, mul_sub,
    hn, hn.symm, hji, hji.symm, hjn, hjn.symm, pos, neg, middle]

theorem short_parent (i : Fin r) (hi : i.val + 1 < r) :
    ⁅positive R r i, short R r ⟨i.val + 1, hi⟩⁆ = short R r i := by
  have hn : (⟨i.val + 1, hi⟩ : Fin r) ≠ i := by
    intro h
    have hv := congrArg Fin.val h
    change i.val + 1 = i.val at hv
    omega
  simp [positive, hi, short, Ring.lie_def, sub_mul, mul_sub,
    hn, hn.symm, pos, neg, middle]

theorem sum_first_parent (i j : Fin r) (hi : i.val + 1 < r)
    (hij : i.val + 1 < j.val) :
    ⁅positive R r i, sumRoot R r ⟨i.val + 1, hi⟩ j⁆ = sumRoot R r i j := by
  have hn : (⟨i.val + 1, hi⟩ : Fin r) ≠ i := by
    intro h
    have hv := congrArg Fin.val h
    change i.val + 1 = i.val at hv
    omega
  have hji : j ≠ i := by intro h; subst j; omega
  have hjn : j ≠ (⟨i.val + 1, hi⟩ : Fin r) := by
    intro h
    have hv := congrArg Fin.val h
    change j.val = i.val + 1 at hv
    omega
  simp [positive, hi, sumRoot, Ring.lie_def, sub_mul, mul_sub,
    hn, hn.symm, hji, hji.symm, hjn, hjn.symm, pos, neg, middle]

theorem sum_second_parent (i j : Fin r) (hj : j.val + 1 < r)
    (hij : i.val < j.val) :
    ⁅positive R r j, sumRoot R r i ⟨j.val + 1, hj⟩⁆ = sumRoot R r i j := by
  have hn : (⟨j.val + 1, hj⟩ : Fin r) ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    change j.val + 1 = j.val at hv
    omega
  have hji : j ≠ i := by intro h; subst j; omega
  have hni : (⟨j.val + 1, hj⟩ : Fin r) ≠ i := by
    intro h
    have hv := congrArg Fin.val h
    change j.val + 1 = i.val at hv
    omega
  simp [positive, hj, sumRoot, Ring.lie_def, sub_mul, mul_sub,
    hn, hn.symm, hji, hji.symm, hni, hni.symm, pos, neg, middle] <;> abel

/-- The terminal SECOND divided power produces minus the primitive long sum root. -/
theorem terminal_second_difference (i last : Fin r)
    (hlast : last.val + 1 = r) (hi : i ≠ last) :
    CFSGIntegralQuadraticRootOperators.operator R
      (positive R r last) (positiveSecond R r last) 2
      (difference R r i last) = -sumRoot R r i last := by
  have h : ¬ last.val + 1 < r := by omega
  simp [CFSGIntegralQuadraticRootOperators.operator_two, positive, positiveSecond,
    h, difference, sumRoot, sub_mul, mul_sub, hi, hi.symm, pos, neg, middle]
  ext a b
  simp [Matrix.single_apply]
  split_ifs <;> ring

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBUniformRootMatrixArithmetic
