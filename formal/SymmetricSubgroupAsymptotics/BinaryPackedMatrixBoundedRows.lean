import SymmetricSubgroupAsymptotics.BinaryPackedMatrix

/-! Width control for the compact row representation.  Matrix decoding is
injective on bounded rows, and every xor multiplication retains the right
factor's width.  No concrete matrix or finite group is used here. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.BinaryPackedMatrixBoundedRows
open BinaryPackedMatrix

def Bounded {n : ℕ} (A : Rows n) : Prop := ∀ i, A i < 2^n

theorem xorSum_lt (n : ℕ) (l : List ℕ) (h : ∀ a∈l, a<2^n) :
    xorSum l<2^n := by
  induction l with
  | nil => exact Nat.two_pow_pos n
  | cons a l ih =>
    exact Nat.xor_lt_two_pow (h a (by simp))
      (ih (fun b hb=>h b (by simp only [List.mem_cons]; exact Or.inr hb)))

theorem mul_bounded {n : ℕ} (A B : Rows n) (hB : Bounded B) :
    Bounded (BinaryPackedMatrix.mul A B) := by
  intro i
  apply xorSum_lt
  intro a ha
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ha
  split
  · exact hB k
  · exact Nat.two_pow_pos n

theorem decode_injective_of_bounded {n : ℕ} (A B : Rows n)
    (hA : Bounded A) (hB : Bounded B) (he : decode A=decode B) : A=B := by
  funext i
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<n
  · have h := congrFun (congrFun he i) (⟨j,hj⟩ : Fin n)
    change bit (A i) j=bit (B i) j at h
    cases ha : (A i).testBit j <;> cases hb : (B i).testBit j <;>
      simp [bit,ha,hb] at h ⊢
  · have hn : n≤j := Nat.le_of_not_gt hj
    have hp : 2^n≤2^j := Nat.pow_le_pow_right (by decide) hn
    rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le (hA i) hp),
      Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le (hB i) hp)]

theorem foldl_bounded {n : ℕ} {ι : Type*} (l : List ι)
    (F : ι→Rows n→Rows n) (hF : ∀ i A, Bounded A→Bounded (F i A))
    (A : Rows n) (hA : Bounded A) : Bounded (l.foldl (fun B i=>F i B) A) := by
  induction l generalizing A with
  | nil => exact hA
  | cons i l ih => exact ih (F i A) (hF i A hA)

end SymmetricSubgroupAsymptotics.BinaryPackedMatrixBoundedRows
