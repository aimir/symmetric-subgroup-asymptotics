import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreEF
import Mathlib.Tactic.NoncommRing

/-! Exact support identities of actual B positive roots. They prove the
extra fourth conjugation coefficient vanishes on simple generators, and
supply the short-root length-three Serre calculations. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
variable (R : Type*) [CommRing R] (r : ℕ)

theorem positive_lower_left (i a b : Fin r) : positive R r i (neg r a) (pos r b)=0 := by
  by_cases hi : i.val+1<r <;> simp [positive,hi,pos,neg,middle,Matrix.single]

theorem positive_upper_right (i a b : Fin r) : positive R r i (pos r a) (neg r b)=0 := by
  by_cases hi : i.val+1<r <;> simp [positive,hi,pos,neg,middle,Matrix.single]

theorem positive_middle_pos (i b : Fin r) : positive R r i (middle r) (pos r b)=0 := by
  by_cases hi : i.val+1<r <;> simp [positive,hi,pos,neg,middle,Matrix.single]

theorem positive_neg_middle (i a : Fin r) : positive R r i (neg r a) (middle r)=0 := by
  by_cases hi : i.val+1<r <;> simp [positive,hi,pos,neg,middle,Matrix.single]

theorem positive_middle_middle (i : Fin r) : positive R r i (middle r) (middle r)=0 := by
  by_cases hi : i.val+1<r <;> simp [positive,hi,pos,neg,middle,Matrix.single]

theorem positive_left_below (i a b : Fin r) (hab : b.val≤a.val) :
    positive R r i (pos r a) (pos r b)=0 := by
  by_cases hi : i.val+1<r
  · have hne : ¬(i=a ∧ (⟨i.val+1,hi⟩ : Fin r)=b) := by
      rintro ⟨ha,hb⟩
      have hva := congrArg Fin.val ha
      have hvb := congrArg Fin.val hb
      change i.val+1=b.val at hvb
      omega
    simp [positive,hi,Matrix.single,pos,neg,middle,hne]
  · simp [positive,hi,Matrix.single,pos,neg,middle]

theorem positive_right_above (i a b : Fin r) (hab : a.val≤b.val) :
    positive R r i (neg r a) (neg r b)=0 := by
  by_cases hi : i.val+1<r
  · have hne : ¬((⟨i.val+1,hi⟩ : Fin r)=a ∧ i=b) := by
      rintro ⟨ha,hb⟩
      have hva := congrArg Fin.val ha
      have hvb := congrArg Fin.val hb
      change i.val+1=a.val at hva
      omega
    simp [positive,hi,Matrix.single,pos,neg,middle,hne]
  · simp [positive,hi,Matrix.single,pos,neg,middle]

theorem positive_sandwich (i j : Fin r) : positive R r i*positive R r j*positive R r i=0 := by
  by_cases hi : i.val+1<r
  · let a : Fin r := ⟨i.val+1,hi⟩
    have hl := positive_left_below R r j a i (by change i.val ≤ i.val+1;omega)
    have hr := positive_right_above R r j i a (by change i.val ≤ i.val+1;omega)
    have hei : positive R r i=Matrix.single (pos r i) (pos r a) 1-
        Matrix.single (neg r a) (neg r i) 1 := by simp only [positive,dif_pos hi];rfl
    rw [hei]
    simp only [sub_mul,mul_sub,Matrix.single_mul_mul_single,one_mul,mul_one,
      hl,hr,positive_upper_right,positive_lower_left,Matrix.single_zero,
      sub_self,sub_zero]
  · have hei : positive R r i=Matrix.single (pos r i) (middle r) 1-
        Matrix.single (middle r) (neg r i) 2 := by simp only [positive,dif_neg hi]
    rw [hei]
    simp only [sub_mul,mul_sub,Matrix.single_mul_mul_single,one_mul,mul_one,
      positive_middle_pos,positive_middle_middle,positive_lower_left,positive_neg_middle,
      mul_zero,zero_mul,Matrix.single_zero,sub_self,sub_zero]

theorem positive_mul_other_second (i j : Fin r) :
    positive R r i*positive R r j*positiveSecond R r i=0 := by
  by_cases hi : i.val+1<r
  · simp only [positiveSecond,if_pos hi,mul_zero]
  · have hei : positive R r i=Matrix.single (pos r i) (middle r) 1-
        Matrix.single (middle r) (neg r i) 2 := by simp only [positive,dif_neg hi]
    rw [hei]
    simp only [positiveSecond,if_neg hi,sub_mul,
      Matrix.single_mul_mul_single,positive_middle_pos,positive_lower_left,
      mul_zero,zero_mul,Matrix.single_zero,sub_self]

theorem second_mul_other_positive (i j : Fin r) :
    positiveSecond R r i*positive R r j*positive R r i=0 := by
  by_cases hi : i.val+1<r
  · simp only [positiveSecond,if_pos hi,zero_mul]
  · have hei : positive R r i=Matrix.single (pos r i) (middle r) 1-
        Matrix.single (middle r) (neg r i) 2 := by simp only [positive,dif_neg hi]
    rw [hei]
    simp only [positiveSecond,if_neg hi,mul_sub,
      Matrix.single_mul_mul_single,positive_lower_left,positive_neg_middle,
      mul_zero,zero_mul,Matrix.single_zero,sub_self]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
