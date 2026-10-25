import SymmetricSubgroupAsymptotics.AffineClassOrderNumerics
import SymmetricSubgroupAsymptotics.AffinePrimePowerClassNumerics

/-! One additional power of five in the uniform affine order budgets.
These scalar statements apply to the same actual subgroup order bounds;
no component capacity or class-count assumption is introduced. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.AffineClassOnePowerGapNumerics

theorem degree_cube_gap (n : ℕ) (hn : 5 ≤ n) : n ^ 3 ≤ 5 ^ (n - 2) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hlinear : 2 * (n + 1) ≤ 3 * n := by omega
    have hpower := Nat.pow_le_pow_left hlinear 3
    have hstep : (n + 1) ^ 3 ≤ 5 * n ^ 3 := by
      have hb : 2 ^ 3 * (n + 1) ^ 3 ≤ 2 ^ 3 * (5 * n ^ 3) := by
        calc
          2 ^ 3 * (n + 1) ^ 3 = (2 * (n + 1)) ^ 3 := (mul_pow _ _ _).symm
          _ ≤ (3 * n) ^ 3 := hpower
          _ = 3 ^ 3 * n ^ 3 := mul_pow _ _ _
          _ ≤ (5 * 2 ^ 3) * n ^ 3 := Nat.mul_le_mul_right _ (by norm_num)
          _ = 2 ^ 3 * (5 * n ^ 3) := by ring
      exact Nat.le_of_mul_le_mul_left hb (by norm_num : 0 < (2 : ℕ) ^ 3)
    calc
      (n + 1) ^ 3 ≤ 5 * n ^ 3 := hstep
      _ ≤ 5 * 5 ^ (n - 2) := Nat.mul_le_mul_left 5 ih
      _ = 5 ^ ((n + 1) - 2) := by
        rw [show (n + 1) - 2 = (n - 2) + 1 by omega, pow_succ]
        exact Nat.mul_comm _ _

theorem square_degree_gap (p : ℕ) (hp : 5 ≤ p) : p ^ 18 ≤ 5 ^ (p ^ 2 - 2) := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ p hp ih =>
    have hscale : (2 : ℕ) ^ 18 ≤ 5 ^ (2 * p + 1) :=
      (by norm_num : (2 : ℕ) ^ 18 ≤ 5 ^ 11).trans
        (Nat.pow_le_pow_right (by decide : 0 < (5 : ℕ)) (by omega))
    calc
      (p + 1) ^ 18 ≤ (2 * p) ^ 18 := Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ 18 * p ^ 18 := mul_pow _ _ _
      _ ≤ 5 ^ (2 * p + 1) * 5 ^ (p ^ 2 - 2) := Nat.mul_le_mul hscale ih
      _ = 5 ^ ((p + 1) ^ 2 - 2) := by
        rw [← pow_add]
        congr 1
        have hs := Nat.sub_add_cancel (show 2 ≤ p ^ 2 by nlinarith)
        have hs' := Nat.sub_add_cancel (show 2 ≤ (p + 1) ^ 2 by nlinarith)
        nlinarith

theorem cube_degree_gap (p : ℕ) (hp : 3 ≤ p) : p ^ 36 ≤ 5 ^ (p ^ 3 - 2) := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ p hp ih =>
    have hscale : (2 : ℕ) ^ 36 ≤ 5 ^ (3 * p ^ 2 + 3 * p + 1) :=
      (by norm_num : (2 : ℕ) ^ 36 ≤ 5 ^ 37).trans
        (Nat.pow_le_pow_right (by decide : 0 < (5 : ℕ)) (by nlinarith))
    calc
      (p + 1) ^ 36 ≤ (2 * p) ^ 36 := Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ 36 * p ^ 36 := mul_pow _ _ _
      _ ≤ 5 ^ (3 * p ^ 2 + 3 * p + 1) * 5 ^ (p ^ 3 - 2) := Nat.mul_le_mul hscale ih
      _ = 5 ^ ((p + 1) ^ 3 - 2) := by
        rw [← pow_add]
        congr 1
        have hp3 : 27 ≤ p ^ 3 := by simpa using Nat.pow_le_pow_left hp 3
        have hsp3 : 27 ≤ (p + 1) ^ 3 := by
          simpa using Nat.pow_le_pow_left (show 3 ≤ p + 1 by omega) 3
        have hs := Nat.sub_add_cancel (show 2 ≤ p ^ 3 by omega)
        have hs' := Nat.sub_add_cancel (show 2 ≤ (p + 1) ^ 3 by omega)
        nlinarith

theorem three_succ_sq_add_four_le (l : ℕ) (hl : 7 ≤ l) :
    3 * (l + 1) ^ 2 + 4 ≤ 2 * 2 ^ l := by
  induction l, hl using Nat.le_induction with
  | base => norm_num
  | succ l hl ih =>
    calc
      3 * (l + 1 + 1) ^ 2 + 4 ≤ 2 * (3 * (l + 1) ^ 2 + 4) := by nlinarith
      _ ≤ 2 * (2 * 2 ^ l) := Nat.mul_le_mul_left 2 ih
      _ = 2 * 2 ^ (l + 1) := by rw [pow_succ]; ring

theorem domain_pow_log_cube_gap (n : ℕ) (hn : 64 ≤ n) :
    (n * n ^ Nat.log 2 n) ^ 3 ≤ 5 ^ (n - 2) := by
  by_cases h64 : n = 64
  · subst n
    norm_num
  by_cases h65 : n = 65
  · subst n
    norm_num
  have hn66 : 66 ≤ n := by omega
  let l := Nat.log 2 n
  have hn0 : n ≠ 0 := by omega
  have hnupper : n ≤ 2 ^ (l + 1) :=
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).le
  have hpower : 2 ^ l ≤ n := Nat.pow_log_le_self 2 hn0
  have horder : n * n ^ Nat.log 2 n ≤ 2 ^ ((l + 1) ^ 2) := by
    calc
      n * n ^ Nat.log 2 n = n ^ (l + 1) := by dsimp only [l]; rw [pow_succ']
      _ ≤ (2 ^ (l + 1)) ^ (l + 1) := Nat.pow_le_pow_left hnupper _
      _ = 2 ^ ((l + 1) ^ 2) := by rw [← pow_mul, pow_two]
  by_cases hl : l ≤ 6
  · have h49 : (l + 1) ^ 2 ≤ 49 := by nlinarith
    calc
      (n * n ^ Nat.log 2 n) ^ 3 ≤ (2 ^ ((l + 1) ^ 2)) ^ 3 := Nat.pow_le_pow_left horder _
      _ ≤ ((2 : ℕ) ^ 49) ^ 3 := Nat.pow_le_pow_left
        (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) h49) _
      _ ≤ 5 ^ 64 := by norm_num
      _ ≤ 5 ^ (n - 2) := Nat.pow_le_pow_right (by decide : 0 < (5 : ℕ)) (by omega)
  · have hl7 : 7 ≤ l := by omega
    have hsmall := three_succ_sq_add_four_le l hl7
    have hexponent : 3 * (l + 1) ^ 2 ≤ 2 * (n - 2) := by omega
    calc
      (n * n ^ Nat.log 2 n) ^ 3 ≤ (2 ^ ((l + 1) ^ 2)) ^ 3 := Nat.pow_le_pow_left horder _
      _ = 2 ^ (3 * (l + 1) ^ 2) := by rw [← pow_mul]; congr 1; ring
      _ ≤ 2 ^ (2 * (n - 2)) := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hexponent
      _ = 4 ^ (n - 2) := by rw [pow_mul]; norm_num
      _ ≤ 5 ^ (n - 2) := Nat.pow_le_pow_left (by decide : (4 : ℕ) ≤ 5) _

end SymmetricSubgroupAsymptotics.AffineClassOnePowerGapNumerics
