import SymmetricSubgroupAsymptotics.FiniteGroupBinaryOrderGenerators
import Mathlib.Data.Nat.Choose.Basic

/-! One component order cube pays the ordinary generator half-degree
bound for every product-action factor count at least two. The full
factorial is retained; no classification of product actions is used. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.ComponentOrderCubeOrdinaryNumerics

theorem factorial_le_two_pow_choose (k : ℕ) : k.factorial ≤ 2^(k.choose 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.factorial_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    exact Nat.mul_le_mul (by have h:=k.lt_two_pow_self; omega) ih

theorem exponent_le_half_power (b k : ℕ) (hb : 4 ≤ b) (hk : 2 ≤ k) :
    2*(k*(b-1)+k.choose 2) ≤ b^k := by
  induction k, hk using Nat.le_induction with
  | base =>
    have hsub : b-1+1=b := by omega
    norm_num [pow_two]
    nlinarith
  | succ k hk ih =>
    have hsub : 3 ≤ b-1 := by omega
    have he : 2*(k+(b-1)) ≤ b^k := by
      have hsmall : k+(b-1) ≤ k*(b-1) := by nlinarith
      exact (Nat.mul_le_mul_left 2 hsmall).trans
        ((Nat.mul_le_mul_left 2 (Nat.le_add_right (k*(b-1)) (k.choose 2))).trans ih)
    rw [Nat.choose_succ_succ, Nat.choose_one_right, pow_succ]
    have hbpow : 2*b^k ≤ b^k*b := by
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_right (b^k) (show 2 ≤ b by omega)
    nlinarith

theorem component_le_two_pow (s b : ℕ) (h : s^3 ≤ 5^(b-1)) : s ≤ 2^(b-1) := by
  have hp : s^3 ≤ (2^(b-1))^3 := by
    calc
      s^3 ≤ 5^(b-1) := h
      _ ≤ 8^(b-1) := Nat.pow_le_pow_left (by decide) _
      _ = (2^(b-1))^3 := by rw [←pow_mul]; rw [Nat.mul_comm]; exact (pow_mul 2 3 (b-1)).symm
  exact (Nat.pow_le_pow_iff_left (by decide : (3:ℕ) ≠ 0)).mp hp

theorem genRank_half_degree_of_order_cube (G : Type) [Group G] [Finite G]
    (s b k : ℕ) (hb : 4 ≤ b) (hk : 2 ≤ k)
    (hbase : s^3 ≤ 5^(b-1)) (horder : Nat.card G ≤ s^k*k.factorial) :
    2*MarkedC4.genRank G ≤ b^k := by
  have hc : Nat.card G ≤ 2^(k*(b-1)+k.choose 2) := by
    calc
      Nat.card G ≤ s^k*k.factorial := horder
      _ ≤ (2^(b-1))^k*2^(k.choose 2) := Nat.mul_le_mul
        (Nat.pow_le_pow_left (component_le_two_pow s b hbase) k) (factorial_le_two_pow_choose k)
      _ = 2^(k*(b-1)+k.choose 2) := by rw [←pow_mul, ←pow_add]; congr 1; ring
  exact (Nat.mul_le_mul_left 2
    (FiniteGroupBinaryOrderGenerators.genRank_le_of_card_le_two_pow G _ hc)).trans
      (exponent_le_half_power b k hb hk)

end SymmetricSubgroupAsymptotics.ComponentOrderCubeOrdinaryNumerics
