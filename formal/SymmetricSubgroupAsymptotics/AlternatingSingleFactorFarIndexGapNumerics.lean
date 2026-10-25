import SymmetricSubgroupAsymptotics.AlternatingSharpSquareFibonacciNumerics
import Mathlib.Tactic.Linarith

/-! A single alternating factor needs no natural-action hypothesis at
actual degrees b>=2m+2. There is one literal minimum base, followed by
uniform m and b inductions. The complementary index interval is not
assumed empty. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.AlternatingSingleFactorFarIndexGapNumerics

private theorem fib_next_le (m : ℕ) : Nat.fib (m+2) ≤ 2*Nat.fib (m+1) := by
  rw [Nat.fib_add_two]
  have h := Nat.fib_le_fib_succ (n := m)
  omega

private theorem minimum_binary_gap (m : ℕ) (hm : 5 ≤ m) :
    (2^(2*m+2)*(4*Nat.fib (m+1)))^3 ≤ 5^(4*m+2) := by
  induction m,hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have hstep : 2^(2*(m+1)+2)*(4*Nat.fib (m+1+1)) ≤
        8*(2^(2*m+2)*(4*Nat.fib (m+1))) := by
      calc
        2^(2*(m+1)+2)*(4*Nat.fib (m+1+1)) =
            (4*2^(2*m+2))*(4*Nat.fib (m+2)) := by
          rw [show 2*(m+1)+2=(2*m+2)+2 by omega,pow_add]
          ring
        _ ≤ (4*2^(2*m+2))*(4*(2*Nat.fib (m+1))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 4 (fib_next_le m))
        _ = 8*(2^(2*m+2)*(4*Nat.fib (m+1))) := by ring
    calc
      (2^(2*(m+1)+2)*(4*Nat.fib (m+1+1)))^3 ≤
          (8*(2^(2*m+2)*(4*Nat.fib (m+1))))^3 := Nat.pow_le_pow_left hstep 3
      _ = 8^3*(2^(2*m+2)*(4*Nat.fib (m+1)))^3 := mul_pow _ _ _
      _ ≤ 8^3*5^(4*m+2) := Nat.mul_le_mul_left _ ih
      _ ≤ 5^4*5^(4*m+2) := Nat.mul_le_mul_right _ (by norm_num : (8:ℕ)^3 ≤ 5^4)
      _ = 5^(4*(m+1)+2) := by rw [←pow_add]; congr 1; omega

theorem binary_product_cube_gap (m b : ℕ) (hm : 5 ≤ m) (hdegree : 2*m+2 ≤ b) :
    (2^b*(4*Nat.fib (m+1)))^3 ≤ 5^(2*b-2) := by
  induction b,hdegree using Nat.le_induction with
  | base =>
    simpa only [show 2*(2*m+2)-2=4*m+2 by omega] using minimum_binary_gap m hm
  | succ b hb ih =>
    calc
      (2^(b+1)*(4*Nat.fib (m+1)))^3 = 8*(2^b*(4*Nat.fib (m+1)))^3 := by
        rw [pow_succ]; ring
      _ ≤ 8*5^(2*b-2) := Nat.mul_le_mul_left _ ih
      _ ≤ 25*5^(2*b-2) := Nat.mul_le_mul_right _ (by decide : (8:ℕ) ≤ 25)
      _ = 5^(2*(b+1)-2) := by
        rw [show 2*(b+1)-2=(2*b-2)+2 by omega,pow_add]
        ring

theorem ternary_product_cube_gap (m b : ℕ) (hm : 5 ≤ m) (hdegree : 2*m+2 ≤ b) :
    (3^b*(4*Nat.fib (m+1)))^3 ≤ 5^(3*b-2) := by
  have hbinary := binary_product_cube_gap m b hm hdegree
  have hthree : (3^b)^3=27^b := by rw [←pow_mul,Nat.mul_comm b 3,pow_mul]; norm_num
  have htwo : (2^b)^3=8^b := by rw [←pow_mul,Nat.mul_comm b 3,pow_mul]; norm_num
  have h27 : (3^b)^3 ≤ 5^b*(2^b)^3 := by
    rw [hthree,htwo,←mul_pow]
    exact Nat.pow_le_pow_left (by decide : (27:ℕ) ≤ 5*8) b
  calc
    (3^b*(4*Nat.fib (m+1)))^3 = (3^b)^3*(4*Nat.fib (m+1))^3 := mul_pow _ _ _
    _ ≤ (5^b*(2^b)^3)*(4*Nat.fib (m+1))^3 := Nat.mul_le_mul_right _ h27
    _ = 5^b*(2^b*(4*Nat.fib (m+1)))^3 := by rw [mul_pow]; ring
    _ ≤ 5^b*5^(2*b-2) := Nat.mul_le_mul_left _ hbinary
    _ = 5^(3*b-2) := by rw [←pow_add]; congr 1; omega

end SymmetricSubgroupAsymptotics.AlternatingSingleFactorFarIndexGapNumerics
