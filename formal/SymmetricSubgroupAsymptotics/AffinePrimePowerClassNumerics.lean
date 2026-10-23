import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Uniform squared- and cubed-degree affine order budgets. Only their
initial prime bases five/three are numerical; all larger bases are
handled by the same doubling estimate. Primality is unnecessary here. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.AffinePrimePowerClassNumerics

theorem square_degree_budget (p : ℕ) (hp : 5 ≤ p) : p^18 ≤ 5^(p^2-1) := by
  induction p,hp using Nat.le_induction with
  | base => norm_num
  | succ p hp ih =>
    have hscale : (2:ℕ)^18 ≤ 5^(2*p+1) :=
      (by norm_num : (2:ℕ)^18 ≤ 5^11).trans
        (Nat.pow_le_pow_right (by decide : 0 < (5:ℕ)) (by omega))
    calc
      (p+1)^18 ≤ (2*p)^18 := Nat.pow_le_pow_left (by omega) _
      _ = 2^18*p^18 := mul_pow _ _ _
      _ ≤ 5^(2*p+1)*5^(p^2-1) := Nat.mul_le_mul hscale ih
      _ = 5^((p+1)^2-1) := by
        rw [← pow_add]
        congr 1
        have hs := Nat.sub_add_cancel (show 1 ≤ p^2 by nlinarith)
        have hs' := Nat.sub_add_cancel (show 1 ≤ (p+1)^2 by nlinarith)
        nlinarith

theorem cube_degree_budget (p : ℕ) (hp : 3 ≤ p) : p^36 ≤ 5^(p^3-1) := by
  induction p,hp using Nat.le_induction with
  | base => norm_num
  | succ p hp ih =>
    have hscale : (2:ℕ)^36 ≤ 5^(3*p^2+3*p+1) :=
      (by norm_num : (2:ℕ)^36 ≤ 5^37).trans
        (Nat.pow_le_pow_right (by decide : 0 < (5:ℕ)) (by nlinarith))
    calc
      (p+1)^36 ≤ (2*p)^36 := Nat.pow_le_pow_left (by omega) _
      _ = 2^36*p^36 := mul_pow _ _ _
      _ ≤ 5^(3*p^2+3*p+1)*5^(p^3-1) := Nat.mul_le_mul hscale ih
      _ = 5^((p+1)^3-1) := by
        rw [← pow_add]
        congr 1
        have hs := Nat.sub_add_cancel (show 1 ≤ p^3 by
          exact Nat.succ_le_of_lt (pow_pos (by omega) _))
        have hs' := Nat.sub_add_cancel (show 1 ≤ (p+1)^3 by
          exact Nat.succ_le_of_lt (pow_pos (by omega) _))
        nlinarith

end SymmetricSubgroupAsymptotics.AffinePrimePowerClassNumerics
