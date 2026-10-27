import SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
import SymmetricSubgroupAsymptotics.CFSGIntegralSquareZeroOperators

/-! Uniform natural matrix arithmetic for the EXACT source parent paths.
All identities hold over every commutative ring. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUniformRootMatrixArithmetic
open CFSGSymplecticSerreMatrices
variable (R : Type*) [CommRing R] (r : ℕ)

def difference (i j : Fin r) : Mat R r :=
  Matrix.single (.inl i) (.inl j) 1-Matrix.single (.inr j) (.inr i) 1

def long (i : Fin r) : Mat R r := Matrix.single (.inl i) (.inr i) 1

def sumRoot (i j : Fin r) : Mat R r :=
  Matrix.single (.inl i) (.inr j) 1+Matrix.single (.inl j) (.inr i) 1

theorem difference_parent (i j : Fin r) (hi : i.val+1<r) (hij : i.val+1<j.val) :
    ⁅positive R r i,difference R r ⟨i.val+1,hi⟩ j⁆=difference R r i j := by
  have hn : (⟨i.val+1,hi⟩ : Fin r)≠i := by
    intro h
    have hv := congrArg Fin.val h
    change i.val+1=i.val at hv
    omega
  have hji : j≠i := by intro h; subst j;omega
  have hjn : j≠(⟨i.val+1,hi⟩ : Fin r) := by
    intro h
    have hv := congrArg Fin.val h
    change j.val=i.val+1 at hv
    omega
  simp [positive,hi,difference,Ring.lie_def,sub_mul,mul_sub,hn,(Ne.symm hn),
    hji,(Ne.symm hji),hjn,(Ne.symm hjn)]

theorem sum_parent (i j : Fin r) (hi : i.val+1<r) (hij : i.val+1<j.val) :
    ⁅positive R r i,sumRoot R r ⟨i.val+1,hi⟩ j⁆=sumRoot R r i j := by
  have hn : (⟨i.val+1,hi⟩ : Fin r)≠i := by
    intro h
    have hv := congrArg Fin.val h
    change i.val+1=i.val at hv
    omega
  have hji : j≠i := by intro h; subst j;omega
  have hjn : j≠(⟨i.val+1,hi⟩ : Fin r) := by
    intro h
    have hv := congrArg Fin.val h
    change j.val=i.val+1 at hv
    omega
  simp [positive,hi,sumRoot,Ring.lie_def,sub_mul,mul_sub,add_mul,mul_add,
    hn,(Ne.symm hn),hji,(Ne.symm hji),hjn,(Ne.symm hjn)]

theorem adjacent_sum_parent (i : Fin r) (hi : i.val+1<r) :
    ⁅positive R r i,long R r ⟨i.val+1,hi⟩⁆=sumRoot R r i ⟨i.val+1,hi⟩ := by
  have hn : (⟨i.val+1,hi⟩ : Fin r)≠i := by
    intro h
    have hv := congrArg Fin.val h
    change i.val+1=i.val at hv
    omega
  simp [positive,hi,sumRoot,long,Ring.lie_def,sub_mul,mul_sub,hn,(Ne.symm hn)]

theorem long_divided_parent (i : Fin r) (hi : i.val+1<r) :
    CFSGIntegralSquareZeroOperators.operator R (positive R r i) 2
      (long R r ⟨i.val+1,hi⟩)=long R r i := by
  have hn : (⟨i.val+1,hi⟩ : Fin r)≠i := by
    intro h
    have hv := congrArg Fin.val h
    change i.val+1=i.val at hv
    omega
  simp [CFSGIntegralSquareZeroOperators.operator_two,positive,hi,long,
    sub_mul,mul_sub,hn,(Ne.symm hn)]

theorem long_bracket_parent (i : Fin r) (hi : i.val+1<r) :
    ⁅positive R r i,sumRoot R r i ⟨i.val+1,hi⟩⁆=(2:ℕ) • long R r i := by
  have hn : (⟨i.val+1,hi⟩ : Fin r)≠i := by
    intro h
    have hv := congrArg Fin.val h
    change i.val+1=i.val at hv
    omega
  simp [positive,hi,sumRoot,long,Ring.lie_def,sub_mul,mul_sub,add_mul,mul_add,
    hn,(Ne.symm hn),two_smul]

end SymmetricSubgroupAsymptotics.CFSGSymplecticUniformRootMatrixArithmetic
