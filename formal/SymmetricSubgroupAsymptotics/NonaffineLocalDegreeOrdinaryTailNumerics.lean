import SymmetricSubgroupAsymptotics.PrimitiveProductOrdinaryTailNumerics

/-! Uniform dyadic scalar budgets for a LARGE LOCAL nonaffine component.
They control arbitrary top degrees through separate logarithmic scaling;
there are no action rows or supplied scalar-fit hypotheses. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.NonaffineLocalDegreeOrdinaryTailNumerics

private theorem polynomial_step (m : ℕ) (hm : 10 ≤ m) :
    9*(m+3)*(2*(m+2)^2+10*(m+2)+3)^2 ≤
      4*(9*(m+2)*(2*(m+1)^2+10*(m+1)+3)^2) := by
  obtain ⟨k,rfl⟩ : ∃ k : ℕ, m = k+10 := ⟨m-10,by omega⟩
  nlinarith only [Nat.zero_le (k^5),Nat.zero_le (k^4),Nat.zero_le (k^3),
    Nat.zero_le (k^2),Nat.zero_le k]

private theorem cubic_step (m : ℕ) (hm : 10 ≤ m) :
    16*(m+3)*(2*(m+2)+5)^2 ≤ 4*(16*(m+2)*(2*(m+1)+5)^2) := by
  obtain ⟨k,rfl⟩ : ∃ k : ℕ, m = k+10 := ⟨m-10,by omega⟩
  nlinarith only [Nat.zero_le (k^3),Nat.zero_le (k^2),Nat.zero_le k]

theorem linear_budget (m : ℕ) (hm : 10 ≤ m) : 9*(m+2) ≤ 2^m :=
  (show 9*(m+2) ≤ 36*(m+1) by omega).trans
    (PrimitiveProductOrdinaryTailNumerics.linear_budget m hm)

/-- The doubled polynomial includes the actual top-ceiling error. -/
theorem polynomial_budget (m : ℕ) (hm : 10 ≤ m) :
    9*(m+2)*(2*(m+1)^2+10*(m+1)+3)^2 ≤ 16*4^m := by
  induction m,hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    calc
      9*(m+1+2)*(2*(m+1+1)^2+10*(m+1+1)+3)^2 ≤
          4*(9*(m+2)*(2*(m+1)^2+10*(m+1)+3)^2) := by
        simpa only [Nat.add_assoc] using polynomial_step m hm
      _ ≤ 4*(16*4^m) := Nat.mul_le_mul_left _ ih
      _ = 16*4^(m+1) := by rw [pow_succ]; omega

/-- The one-factor branch has only linear outer-order multiplicity. -/
theorem cubic_budget (m : ℕ) (hm : 10 ≤ m) :
    16*(m+2)*(2*(m+1)+5)^2 ≤ 4^m := by
  induction m,hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    calc
      16*(m+1+2)*(2*(m+1+1)+5)^2 ≤
          4*(16*(m+2)*(2*(m+1)+5)^2) := by
        simpa only [Nat.add_assoc] using cubic_step m hm
      _ ≤ 4*4^m := Nat.mul_le_mul_left _ ih
      _ = 4^(m+1) := by rw [pow_succ]; omega

end SymmetricSubgroupAsymptotics.NonaffineLocalDegreeOrdinaryTailNumerics
