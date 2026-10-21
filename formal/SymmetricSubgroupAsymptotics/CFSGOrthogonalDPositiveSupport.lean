import SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
import Mathlib.Tactic.NoncommRing

/-! The original natural D-root supports force every positive simple-root
sandwich to vanish. No source Serre-quotient injectivity is used. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
variable (R : Type*) [CommRing R] (r : ℕ)

theorem positive_lower_left (i a b : Fin r) : positive R r i (Sum.inr a) (Sum.inl b)=0 := by
  by_cases hi : i.val+1<r <;> simp [positive,hi,Matrix.single]

theorem positive_left_below (i a b : Fin r) (hab : b.val≤a.val) :
    positive R r i (Sum.inl a) (Sum.inl b)=0 := by
  by_cases hi : i.val+1<r
  · have hne : ¬(i=a ∧ (⟨i.val+1,hi⟩ : Fin r)=b) := by
      rintro ⟨ha,hb⟩
      have hva := congrArg Fin.val ha
      have hvb := congrArg Fin.val hb
      change i.val+1=b.val at hvb
      omega
    simp [positive,hi,Matrix.single,hne]
  · simp [positive,hi,Matrix.single]

theorem positive_right_above (i a b : Fin r) (hab : a.val≤b.val) :
    positive R r i (Sum.inr a) (Sum.inr b)=0 := by
  by_cases hi : i.val+1<r
  · have hne : ¬((⟨i.val+1,hi⟩ : Fin r)=a ∧ i=b) := by
      rintro ⟨ha,hb⟩
      have hva := congrArg Fin.val ha
      have hvb := congrArg Fin.val hb
      change i.val+1=a.val at hva
      omega
    simp [positive,hi,Matrix.single,hne]
  · simp [positive,hi,Matrix.single]

theorem positive_cross_diagonal (i a : Fin r) : positive R r i (Sum.inl a) (Sum.inr a)=0 := by
  by_cases hi : i.val+1<r <;> simp [positive,hi,Matrix.single,and_comm]

theorem positive_sandwich (i j : Fin r) : positive R r i*positive R r j*positive R r i=0 := by
  by_cases hi : i.val+1<r
  · let a : Fin r := ⟨i.val+1,hi⟩
    let M : Mat R r := Matrix.single (Sum.inl i) (Sum.inl a) 1
    let N : Mat R r := Matrix.single (Sum.inr a) (Sum.inr i) 1
    have he : positive R r i=M-N := by simp only [positive,dif_pos hi];rfl
    have hl : positive R r j (Sum.inl a) (Sum.inl i)=0 :=
      positive_left_below R r j a i (by change i.val ≤ i.val + 1;omega)
    have hr : positive R r j (Sum.inr i) (Sum.inr a)=0 :=
      positive_right_above R r j i a (by change i.val ≤ i.val + 1;omega)
    rw [he]
    calc
      (M-N)*positive R r j*(M-N)=M*positive R r j*M-M*positive R r j*N-
        (N*positive R r j*M-N*positive R r j*N) := by noncomm_ring
      _=0 := by
        simp only [M,N,Matrix.single_mul_mul_single,one_mul,mul_one,hl,hr,
          positive_cross_diagonal,positive_lower_left,Matrix.single_zero,sub_self]
  · let a := previous r i
    let M : Mat R r := Matrix.single (Sum.inl a) (Sum.inr i) 1
    let N : Mat R r := Matrix.single (Sum.inl i) (Sum.inr a) 1
    have he : positive R r i=M-N := by simp only [positive,dif_neg hi];rfl
    rw [he]
    calc
      (M-N)*positive R r j*(M-N)=M*positive R r j*M-M*positive R r j*N-
        (N*positive R r j*M-N*positive R r j*N) := by noncomm_ring
      _=0 := by
        simp only [M,N,Matrix.single_mul_mul_single,one_mul,mul_one,positive_lower_left,
          Matrix.single_zero,sub_self]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
