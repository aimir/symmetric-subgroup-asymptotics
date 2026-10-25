import SymmetricSubgroupAsymptotics.SmallFibreScaledClassEnvelopeNumerics

/-! Exact constant-twelve top capacities for original binary/ternary
fibres. Two seeds and one-step induction retain the actual number of
blocks, with no desired class-capacity hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.SmallFibreTwelveClassEnvelope

theorem binary_gap (n : ℕ) (hn : 10 ≤ n) : (2^n*12)^3 ≤ 5^(2*n-2) := by
  induction n,hn using Nat.le_induction with
  | base => decide +kernel
  | succ n hn ih =>
    calc
      (2^(n+1)*12)^3 = 8*(2^n*12)^3 := by rw [pow_succ]; ring
      _ ≤ 8*5^(2*n-2) := Nat.mul_le_mul_left _ ih
      _ ≤ 25*5^(2*n-2) := Nat.mul_le_mul_right _ (by decide : (8:ℕ)≤25)
      _ = 5^(2*(n+1)-2) := by
        rw [show 2*(n+1)-2=(2*n-2)+2 by omega,pow_add]
        ring

theorem ternary_gap (n : ℕ) (hn : 7 ≤ n) : (3^n*12)^3 ≤ 5^(3*n-2) := by
  induction n,hn using Nat.le_induction with
  | base => decide +kernel
  | succ n hn ih =>
    calc
      (3^(n+1)*12)^3 = 27*(3^n*12)^3 := by rw [pow_succ]; ring
      _ ≤ 27*5^(3*n-2) := Nat.mul_le_mul_left _ ih
      _ ≤ 125*5^(3*n-2) := Nat.mul_le_mul_right _ (by decide : (27:ℕ)≤125)
      _ = 5^(3*(n+1)-2) := by
        rw [show 3*(n+1)-2=(3*n-2)+3 by omega,pow_add]
        ring

end SymmetricSubgroupAsymptotics.SmallFibreTwelveClassEnvelope
