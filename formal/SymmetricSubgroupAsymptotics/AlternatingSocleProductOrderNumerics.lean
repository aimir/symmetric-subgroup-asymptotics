import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! A uniform order budget for at least two alternating socle factors.
This file is purely numerical; actual socle, quotient and degree data
must be supplied by a separate structural theorem. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.AlternatingSocleProductOrderNumerics

theorem cube_le_five_pow (t : ℕ) (ht : 3 ≤ t) : t^3 ≤ 5^t := by
  induction t,ht using Nat.le_induction with
  | base => decide
  | succ t ht ih =>
    have hstep : (t+1)^3 ≤ 5*t^3 := by
      obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le ht
      apply Nat.le.intro (k := 4*u^3+33*u^2+87*u+71)
      ring
    calc
      (t+1)^3 ≤ 5*t^3 := hstep
      _ ≤ 5*5^t := Nat.mul_le_mul_left 5 ih
      _ = 5^(t+1) := by rw [pow_succ]; ring

theorem sixth_power_step (m : ℕ) (hm : 5 ≤ m) : (m+1)^6 ≤ 5^(2*m+1) := by
  induction m,hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have hs : (m+2)^2 ≤ 2*(m+1)^2 := by nlinarith
    calc
      (m+1+1)^6 = ((m+2)^2)^3 := by ring
      _ ≤ (2*(m+1)^2)^3 := Nat.pow_le_pow_left hs 3
      _ = 8*(m+1)^6 := by ring
      _ ≤ 8*5^(2*m+1) := Nat.mul_le_mul_left 8 ih
      _ ≤ 25*5^(2*m+1) := Nat.mul_le_mul_right _ (by decide)
      _ = 5^(2*(m+1)+1) := by
        rw [show 2*(m+1)+1=(2*m+1)+2 by ring,pow_add]
        ring

theorem two_factor_order_cube (m : ℕ) (hm : 5 ≤ m) :
    ((2*m.factorial)^2*2)^3 ≤ 5^(m^2-1) := by
  induction m,hm using Nat.le_induction with
  | base => decide +kernel
  | succ m hm ih =>
    have he : m^2-1+(2*m+1)=(m+1)^2-1 := by
      have h0 : 1 ≤ m^2 := by nlinarith
      have h1 : 1 ≤ (m+1)^2 := by nlinarith
      nlinarith [Nat.sub_add_cancel h0,Nat.sub_add_cancel h1]
    calc
      ((2*(m+1).factorial)^2*2)^3 =
          ((2*m.factorial)^2*2)^3*(m+1)^6 := by rw [Nat.factorial_succ]; ring
      _ ≤ 5^(m^2-1)*5^(2*m+1) :=
        Nat.mul_le_mul ih (sixth_power_step m hm)
      _ = 5^((m+1)^2-1) := by rw [←pow_add,he]

theorem factorial_product_cube (m k : ℕ) (hm : 5 ≤ m) (hk : 2 ≤ k) :
    ((2*m.factorial)^k*k.factorial)^3 ≤ 5^(m^k-1) := by
  induction k,hk using Nat.le_induction with
  | base => simpa only [show (2 : ℕ).factorial=2 by decide] using two_factor_order_cube m hm
  | succ k hk ih =>
    let a := 2*m.factorial
    have ha1 : 1 ≤ a := by have hf := Nat.factorial_pos m; dsimp [a]; omega
    have ha : a^3 ≤ 5^(m^2-1) := by
      have haa : a ≤ a^2*2 := by nlinarith
      exact (Nat.pow_le_pow_left haa 3).trans (two_factor_order_cube m hm)
    have hmpos : 0 < m := by omega
    have hpow : m^2 ≤ m^k := Nat.pow_le_pow_right hmpos hk
    have hbig : 3 ≤ m^k := by
      have hle : m ≤ m^k := Nat.le_self_pow (by omega) m
      omega
    have hkp : k+1 ≤ m^k :=
      (show k+1 ≤ 2^k from Nat.lt_two_pow_self).trans
        (Nat.pow_le_pow_left (by omega : 2 ≤ m) k)
    have hrat : (a*(k+1))^3 ≤ 5^((m-1)*m^k) := by
      have hex : (m^k-1)+m^k ≤ (m-1)*m^k := by
        calc
          _ ≤ m^k+m^k := Nat.add_le_add_right (Nat.sub_le _ _) _
          _ = 2*m^k := by ring
          _ ≤ _ := Nat.mul_le_mul_right _ (by omega : 2 ≤ m-1)
      calc
        (a*(k+1))^3 = a^3*(k+1)^3 := by ring
        _ ≤ 5^(m^k-1)*5^(m^k) := Nat.mul_le_mul
          (ha.trans (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hpow 1)))
          ((Nat.pow_le_pow_left hkp 3).trans (cube_le_five_pow _ hbig))
        _ = 5^((m^k-1)+m^k) := by rw [pow_add]
        _ ≤ _ := Nat.pow_le_pow_right (by decide) hex
    have hsplit : (m^k-1)+(m-1)*m^k=m^(k+1)-1 := by
      have hh : (m-1)*m^k+m^k=m*m^k := by
        rw [←Nat.add_one_mul,Nat.sub_add_cancel (by omega : 1 ≤ m)]
      rw [pow_succ]
      nlinarith [Nat.sub_add_cancel (show 1 ≤ m^k by omega),
        Nat.sub_add_cancel (show 1 ≤ m^k*m by nlinarith)]
    calc
      ((2*m.factorial)^(k+1)*(k+1).factorial)^3 =
          ((2*m.factorial)^k*k.factorial)^3*(a*(k+1))^3 := by
        rw [pow_succ,Nat.factorial_succ]
        dsimp only [a]
        ring
      _ ≤ 5^(m^k-1)*5^((m-1)*m^k) := Nat.mul_le_mul ih hrat
      _ = 5^(m^(k+1)-1) := by rw [←pow_add,hsplit]

end SymmetricSubgroupAsymptotics.AlternatingSocleProductOrderNumerics
