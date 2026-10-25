import SymmetricSubgroupAsymptotics.AlternatingSharpSquareFibonacciNumerics
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Factorial.Basic

/-! Every alternating multiplicity at least two has a small-fibre
class-cube reserve at its ACTUAL degree b>=m^k. No 4096 cutoff is used.
The only small bases are the separately checked five-square pilot. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.AlternatingSharpMultiFactorSmallFibreGapNumerics

private theorem fib_le_binary (n : ℕ) : Nat.fib (n+1) ≤ 2^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    calc
      Nat.fib (n+1+1) = Nat.fib n+Nat.fib (n+1) := Nat.fib_add_two
      _ ≤ 2*Nat.fib (n+1) := by have h := Nat.fib_le_fib_succ (n := n); omega
      _ ≤ 2*2^n := Nat.mul_le_mul_left _ ih
      _ = 2^(n+1) := by rw [pow_succ]; ac_rfl

private theorem exponent_le_power (m : ℕ) (hm : 5 ≤ m) (k : ℕ) (hk : 3 ≤ k) :
    3*(k*m+3*k+k*k)+4 ≤ m^k := by
  induction k,hk using Nat.le_induction with
  | base =>
    have hsq : 25 ≤ m*m := Nat.mul_le_mul hm hm
    have hcube : 25*m ≤ m^3 := by
      simpa only [pow_succ,pow_zero,Nat.one_mul,Nat.mul_assoc] using Nat.mul_le_mul_right m hsq
    nlinarith only [hm,hcube]
  | succ k hk ih =>
    have hkm : 3*m ≤ k*m := Nat.mul_le_mul_right m hk
    have hs : 3*((k+1)*m+3*(k+1)+(k+1)*(k+1))+4 ≤
        2*(3*(k*m+3*k+k*k)+4) := by
      nlinarith only [hm,hk,hkm,Nat.zero_le (k*k)]
    exact hs.trans ((Nat.mul_le_mul_left 2 ih).trans
      ((Nat.mul_le_mul_right (m^k) (by omega : 2 ≤ m)).trans_eq
        (by rw [pow_succ,Nat.mul_comm])))

private theorem factorial_le_binary_square (k : ℕ) : k.factorial ≤ 2^(k*k) :=
  (Nat.factorial_le_pow k).trans
    ((Nat.pow_le_pow_left k.lt_two_pow_self.le k).trans_eq (pow_mul 2 k k).symm)

private theorem envelope_le_binary (m k : ℕ) :
    (4*Nat.fib (m+1))^k*k.factorial ≤ 2^(k*m+3*k+k*k) := by
  have hc : 4*Nat.fib (m+1) ≤ 8*2^m :=
    (Nat.mul_le_mul_left 4 (fib_le_binary m)).trans
      (Nat.mul_le_mul_right _ (by decide : (4:ℕ) ≤ 8))
  calc
    (4*Nat.fib (m+1))^k*k.factorial ≤ (8*2^m)^k*2^(k*k) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hc k) (factorial_le_binary_square k)
    _ = 2^((3+m)*k+k*k) := by
      rw [show (8:ℕ)=2^3 by decide,←pow_add,←pow_mul,←pow_add]
    _ = 2^(k*m+3*k+k*k) := by congr 1; ring

private theorem binary_gap_of_exponent (m k b : ℕ)
    (he : 3*(k*m+3*k+k*k)+4 ≤ b) :
    (2^b*((4*Nat.fib (m+1))^k*k.factorial))^3 ≤ 5^(2*b-2) := by
  have he' : (b+(k*m+3*k+k*k))*3 ≤ 2*(2*b-2) := by omega
  calc
    (2^b*((4*Nat.fib (m+1))^k*k.factorial))^3 ≤
        (2^b*2^(k*m+3*k+k*k))^3 :=
      Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (envelope_le_binary m k)) 3
    _ = 2^((b+(k*m+3*k+k*k))*3) := by rw [←pow_add,←pow_mul]
    _ ≤ 2^(2*(2*b-2)) := Nat.pow_le_pow_right (by decide) he'
    _ = 4^(2*b-2) := by rw [show (4:ℕ)=2^2 by decide,pow_mul]
    _ ≤ 5^(2*b-2) := Nat.pow_le_pow_left (by decide) _

theorem binary_product_cube_gap (m k b : ℕ) (hm : 5 ≤ m) (hk : 2 ≤ k)
    (hdegree : m^k ≤ b) :
    (2^b*((4*Nat.fib (m+1))^k*k.factorial))^3 ≤ 5^(2*b-2) := by
  by_cases hk3 : 3 ≤ k
  · exact binary_gap_of_exponent m k b ((exponent_le_power m hm k hk3).trans hdegree)
  have hk2 : k=2 := by omega
  subst k
  by_cases hm10 : 10 ≤ m
  · apply binary_gap_of_exponent m 2 b
    have hmul : 10*m ≤ m*m := Nat.mul_le_mul_right m hm10
    have hsq : 6*m+34 ≤ m^2 := by nlinarith only [hm10,hmul]
    nlinarith only [hsq,hdegree]
  · have hsmall := AlternatingSharpSquareFibonacciNumerics.binary_product_cube_gap
      m b hm (by omega) hdegree
    simpa only [AlternatingSharpSquareFibonacciNumerics.envelope,Nat.factorial_two] using hsmall

theorem ternary_product_cube_gap (m k b : ℕ) (hm : 5 ≤ m) (hk : 2 ≤ k)
    (hdegree : m^k ≤ b) :
    (3^b*((4*Nat.fib (m+1))^k*k.factorial))^3 ≤ 5^(3*b-2) := by
  have hb : 2 ≤ b := by
    have hm2 : 2 ≤ m := by omega
    have hkpos : 1 ≤ k := by omega
    have h := (Nat.pow_le_pow_right (by omega : 0 < m) hkpos).trans hdegree
    have hmle : m ≤ b := by simpa only [pow_one] using h
    exact hm2.trans hmle
  have hbinary := binary_product_cube_gap m k b hm hk hdegree
  have hthree : (3^b)^3 = 27^b := by
    rw [←pow_mul,Nat.mul_comm b 3,pow_mul]
    norm_num
  have htwo : (2^b)^3 = 8^b := by
    rw [←pow_mul,Nat.mul_comm b 3,pow_mul]
    norm_num
  have h27 : (3^b)^3 ≤ 5^b*(2^b)^3 := by
    rw [hthree,htwo,←mul_pow]
    exact Nat.pow_le_pow_left (by decide : (27:ℕ) ≤ 5*8) b
  calc
    (3^b*((4*Nat.fib (m+1))^k*k.factorial))^3 =
        (3^b)^3*((4*Nat.fib (m+1))^k*k.factorial)^3 := mul_pow _ _ _
    _ ≤ (5^b*(2^b)^3)*((4*Nat.fib (m+1))^k*k.factorial)^3 :=
      Nat.mul_le_mul_right _ h27
    _ = 5^b*(2^b*((4*Nat.fib (m+1))^k*k.factorial))^3 := by rw [mul_pow]; ring
    _ ≤ 5^b*5^(2*b-2) := Nat.mul_le_mul_left _ hbinary
    _ = 5^(3*b-2) := by rw [←pow_add]; congr 1; omega

end SymmetricSubgroupAsymptotics.AlternatingSharpMultiFactorSmallFibreGapNumerics
