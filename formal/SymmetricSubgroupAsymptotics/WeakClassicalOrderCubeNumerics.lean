import SymmetricSubgroupAsymptotics.QuadraticRankOrderCubeNumerics
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum

/-! One common order exponent covers the native B/C/D/twisted-D bounds
at their EXACT root-star dimensions t=r-1 or t=r-2. The separate C2 tail
retains its smaller exponent19. All arithmetic seeds use small powers
and power monotonicity; there is no group/action enumeration. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.WeakClassicalOrderCubeNumerics
open QuadraticRankOrderCubeNumerics

def componentExponent (t : ℕ) : ℕ := 4 * (t + 2) ^ 2 + 4

private theorem exponent_double (t : ℕ) (ht : 2 ≤ t) :
    componentExponent (t + 1) ≤ 2 * componentExponent t := by
  unfold componentExponent
  nlinarith

private theorem binary_even_power_le (b : ℕ) : (2 : ℕ) ^ (2 * b) ≤ 5 ^ b := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left (by decide) b

private theorem seed_23 : (23 : ℕ) ^ (3 * componentExponent 2) ≤ 5 ^ (23 ^ 2 - 1) := by
  change (23 : ℕ) ^ 204 ≤ 5 ^ 528
  calc
    (23 : ℕ) ^ 204 ≤ (5 ^ 2) ^ 204 := Nat.pow_le_pow_left (by decide) 204
    _ = 5 ^ 408 := by rw [←pow_mul]
    _ ≤ 5 ^ 528 := Nat.pow_le_pow_right (by decide) (by decide)

private theorem seed_8 : (8 : ℕ) ^ (3 * componentExponent 3) ≤ 5 ^ (8 ^ 3 - 1) := by
  change (8 : ℕ) ^ 312 ≤ 5 ^ 511
  calc
    (8 : ℕ) ^ 312 = (2 ^ 9) ^ 104 := by
      rw [show (8 : ℕ) = 2 ^ 3 by decide, ←pow_mul, ←pow_mul]
    _ ≤ (5 ^ 4) ^ 104 := Nat.pow_le_pow_left (by decide : (2 : ℕ) ^ 9 ≤ 5 ^ 4) 104
    _ = 5 ^ 416 := by rw [←pow_mul]
    _ ≤ 5 ^ 511 := Nat.pow_le_pow_right (by decide) (by decide)

private theorem seed_5 : (5 : ℕ) ^ (3 * componentExponent 4) ≤ 5 ^ (5 ^ 4 - 1) := by
  change (5 : ℕ) ^ 444 ≤ 5 ^ 624
  exact Nat.pow_le_pow_right (by decide) (by decide)

private theorem seed_4 : (4 : ℕ) ^ (3 * componentExponent 5) ≤ 5 ^ (4 ^ 5 - 1) := by
  change (4 : ℕ) ^ 600 ≤ 5 ^ 1023
  exact (Nat.pow_le_pow_left (by decide : (4 : ℕ) ≤ 5) 600).trans
    (Nat.pow_le_pow_right (by decide) (by decide))

private theorem seed_3 : (3 : ℕ) ^ (3 * componentExponent 6) ≤ 5 ^ (3 ^ 6 - 1) := by
  change (3 : ℕ) ^ 780 ≤ 5 ^ 728
  calc
    (3 : ℕ) ^ 780 = (3 ^ 4) ^ 195 := by rw [←pow_mul]
    _ ≤ (5 ^ 3) ^ 195 := Nat.pow_le_pow_left (by decide : (3 : ℕ) ^ 4 ≤ 5 ^ 3) 195
    _ = 5 ^ 585 := by rw [←pow_mul]
    _ ≤ 5 ^ 728 := Nat.pow_le_pow_right (by decide) (by decide)

private theorem seed_2 : (2 : ℕ) ^ (3 * componentExponent 10) ≤ 5 ^ (2 ^ 10 - 1) := by
  change (2 : ℕ) ^ 1740 ≤ 5 ^ 1023
  exact (binary_even_power_le 870).trans (Nat.pow_le_pow_right (by decide) (by decide))

private theorem large_field (q t : ℕ) (hq : 23 ≤ q) (ht : 2 ≤ t) :
    q ^ (3 * componentExponent t) ≤ 5 ^ (q ^ t - 1) :=
  rank_tail q (by omega) componentExponent 2 exponent_double
    (field_tail 23 2 68 34 (by decide) (binary_even_power_le 34) (by decide) seed_23 q hq) t ht

private theorem field_eight (q t : ℕ) (hq : 8 ≤ q) (ht : 3 ≤ t) :
    q ^ (3 * componentExponent t) ≤ 5 ^ (q ^ t - 1) :=
  rank_tail q (by omega) componentExponent 3 (fun t ht => exponent_double t (by omega))
    (field_tail 8 3 104 52 (by decide) (binary_even_power_le 52) (by decide) seed_8 q hq) t ht

private theorem field_five (q t : ℕ) (hq : 5 ≤ q) (ht : 4 ≤ t) :
    q ^ (3 * componentExponent t) ≤ 5 ^ (q ^ t - 1) :=
  rank_tail q (by omega) componentExponent 4 (fun t ht => exponent_double t (by omega))
    (field_tail 5 4 148 74 (by decide) (binary_even_power_le 74) (by decide) seed_5 q hq) t ht

private theorem field_four (q t : ℕ) (hq : 4 ≤ q) (ht : 5 ≤ t) :
    q ^ (3 * componentExponent t) ≤ 5 ^ (q ^ t - 1) :=
  rank_tail q (by omega) componentExponent 5 (fun t ht => exponent_double t (by omega))
    (field_tail 4 5 200 100 (by decide) (binary_even_power_le 100) (by decide) seed_4 q hq) t ht

private theorem field_three (q t : ℕ) (hq : 3 ≤ q) (ht : 6 ≤ t) :
    q ^ (3 * componentExponent t) ≤ 5 ^ (q ^ t - 1) := by
  by_cases he : q = 3
  · subst q
    exact rank_tail 3 (by decide) componentExponent 6 (fun t ht => exponent_double t (by omega))
      seed_3 t ht
  · exact field_four q t (by omega) (by omega)

def Capacity (q t : ℕ) : Prop :=
  23 ≤ q ∨ (8 ≤ q ∧ 3 ≤ t) ∨ (5 ≤ q ∧ 4 ≤ t) ∨ (4 ≤ q ∧ 5 ≤ t) ∨
    (3 ≤ q ∧ 6 ≤ t) ∨ 10 ≤ t

theorem common_order_cube (q t : ℕ) (hq : 2 ≤ q) (ht : 2 ≤ t) (hc : Capacity q t) :
    q ^ (3 * componentExponent t) ≤ 5 ^ (q ^ t - 1) := by
  rcases hc with h | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | h
  · exact large_field q t h ht
  · exact field_eight q t h h'
  · exact field_five q t h h'
  · exact field_four q t h h'
  · exact field_three q t h h'
  · by_cases he : q = 2
    · subst q
      exact rank_tail 2 (by decide) componentExponent 10 (fun t ht => exponent_double t (by omega))
        seed_2 t h
    · exact field_three q t (by omega) (by omega)

theorem root_power_ge_thirtyTwo (q t : ℕ) (hq : 2 ≤ q) (ht : 2 ≤ t) (hc : Capacity q t) :
    32 ≤ q ^ t := by
  rcases hc with h | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | h
  · exact (by decide : 32 ≤ 23 ^ 2).trans
      ((Nat.pow_le_pow_left h 2).trans (Nat.pow_le_pow_right (by omega) ht))
  · exact (by decide : 32 ≤ 8 ^ 3).trans
      ((Nat.pow_le_pow_left h 3).trans (Nat.pow_le_pow_right (by omega) h'))
  · exact (by decide : 32 ≤ 5 ^ 4).trans
      ((Nat.pow_le_pow_left h 4).trans (Nat.pow_le_pow_right (by omega) h'))
  · exact (by decide : 32 ≤ 4 ^ 5).trans
      ((Nat.pow_le_pow_left h 5).trans (Nat.pow_le_pow_right (by omega) h'))
  · exact (by decide : 32 ≤ 3 ^ 6).trans
      ((Nat.pow_le_pow_left h 6).trans (Nat.pow_le_pow_right (by omega) h'))
  · exact (by decide : 32 ≤ 2 ^ 10).trans
      ((Nat.pow_le_pow_left hq 10).trans (Nat.pow_le_pow_right (by omega) h))

private theorem c_two_dyadic (l : ℕ) (hl : 8 ≤ l) : 4 * 57 * (l + 1) + 9 ≤ 9 * 2 ^ l := by
  induction l, hl using Nat.le_induction with
  | base => norm_num
  | succ l hl ih =>
    calc
      4 * 57 * (l + 1 + 1) + 9 ≤ 2 * (4 * 57 * (l + 1) + 9) := by omega
      _ ≤ 2 * (9 * 2 ^ l) := Nat.mul_le_mul_left 2 ih
      _ = 9 * 2 ^ (l + 1) := by rw [pow_succ]; ring

theorem symplectic_rank_two_order_cube (q : ℕ) (hq : 256 ≤ q) :
    q ^ 57 ≤ 5 ^ (q - 1) := by
  let l := Nat.log 2 q
  have hl : 8 ≤ l := Nat.le_log_of_pow_le (by decide) (by simpa using hq)
  have hu : q ≤ 2 ^ (l + 1) := (Nat.lt_pow_succ_log_self (by decide) q).le
  have hd : 2 ^ l ≤ q := Nat.pow_log_le_self 2 (by omega)
  have he := c_two_dyadic l hl
  have hlarge : 4 * 57 * (l + 1) ≤ 9 * (q - 1) := by omega
  have hp : (q ^ 57) ^ 4 ≤ (5 ^ (q - 1)) ^ 4 := by
    calc
      (q ^ 57) ^ 4 ≤ ((2 ^ (l + 1)) ^ 57) ^ 4 :=
        Nat.pow_le_pow_left (Nat.pow_le_pow_left hu 57) 4
      _ = 2 ^ (4 * 57 * (l + 1)) := by
        rw [←pow_mul, ←pow_mul]
        congr 1
        ring
      _ ≤ 2 ^ (9 * (q - 1)) := Nat.pow_le_pow_right (by decide) hlarge
      _ = (2 ^ 9) ^ (q - 1) := pow_mul _ _ _
      _ ≤ (5 ^ 4) ^ (q - 1) := Nat.pow_le_pow_left (by decide : (2 : ℕ) ^ 9 ≤ 5 ^ 4) _
      _ = (5 ^ (q - 1)) ^ 4 := by rw [←pow_mul, ←pow_mul]; congr 1; ring
  by_contra hn
  have hh := Nat.pow_lt_pow_left (by omega : 5 ^ (q - 1) < q ^ 57) (by decide : 4 ≠ 0)
  omega

end SymmetricSubgroupAsymptotics.WeakClassicalOrderCubeNumerics
