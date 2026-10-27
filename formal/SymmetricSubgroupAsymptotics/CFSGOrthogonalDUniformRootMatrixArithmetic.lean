import SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
import Mathlib.Tactic.Abel

/-! Actual all-rank natural D root-parent arithmetic. Every parent
coefficient is a unit; sum-root matrices retain their skew sign. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformRootMatrixArithmetic
open CFSGOrthogonalDSerreMatrices
variable (R : Type*) [CommRing R] (r : ℕ)

def difference (i j : Fin r) : Mat R r :=
  Matrix.single (.inl i) (.inl j) 1-Matrix.single (.inr j) (.inr i) 1

def sumRoot (i j : Fin r) : Mat R r :=
  Matrix.single (.inl i) (.inr j) 1-Matrix.single (.inl j) (.inr i) 1

theorem difference_parent (i j : Fin r) (hi : i.val+1 < r) (hij : i.val+1 < j.val) :
    ⁅positive R r i,difference R r ⟨i.val+1,hi⟩ j⁆=difference R r i j := by
  have hn : (⟨i.val+1,hi⟩ : Fin r)≠i := by
    intro h
    have hv:=congrArg Fin.val h
    change i.val+1=i.val at hv
    omega
  have hji : j≠i := by intro h; subst j; omega
  have hjn : j≠(⟨i.val+1,hi⟩ : Fin r) := by
    intro h
    have hv:=congrArg Fin.val h
    change j.val=i.val+1 at hv
    omega
  simp [positive,hi,difference,Ring.lie_def,sub_mul,mul_sub,
    hn,Ne.symm hn,hji,Ne.symm hji,hjn,Ne.symm hjn]

theorem sum_left_parent (i j : Fin r) (hi : i.val+1 < r) (hij : i.val+1 < j.val) :
    ⁅positive R r i,sumRoot R r ⟨i.val+1,hi⟩ j⁆=sumRoot R r i j := by
  have hn : (⟨i.val+1,hi⟩ : Fin r)≠i := by
    intro h
    have hv:=congrArg Fin.val h
    change i.val+1=i.val at hv
    omega
  have hji : j≠i := by intro h; subst j; omega
  have hjn : j≠(⟨i.val+1,hi⟩ : Fin r) := by
    intro h
    have hv:=congrArg Fin.val h
    change j.val=i.val+1 at hv
    omega
  simp [positive,hi,sumRoot,Ring.lie_def,sub_mul,mul_sub,
    hn,Ne.symm hn,hji,Ne.symm hji,hjn,Ne.symm hjn]

theorem sum_right_parent (i j : Fin r) (hj : j.val+1 < r) (hij : i.val < j.val) :
    ⁅positive R r j,sumRoot R r i ⟨j.val+1,hj⟩⁆=sumRoot R r i j := by
  have hn : (⟨j.val+1,hj⟩ : Fin r)≠j := by
    intro h
    have hv:=congrArg Fin.val h
    change j.val+1=j.val at hv
    omega
  have hji : j≠i := by intro h; subst j; omega
  have hin : i≠(⟨j.val+1,hj⟩ : Fin r) := by
    intro h
    have hv:=congrArg Fin.val h
    change i.val=j.val+1 at hv
    omega
  simp [positive,hj,sumRoot,Ring.lie_def,sub_mul,mul_sub,
    hn,Ne.symm hn,hji,Ne.symm hji,hin,Ne.symm hin] <;> abel

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformRootMatrixArithmetic
