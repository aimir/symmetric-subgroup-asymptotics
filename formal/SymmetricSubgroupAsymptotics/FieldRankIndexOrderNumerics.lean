import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Converting a literal field-power proper-index lower bound and a
quadratic matrix-dimension upper bound into a logarithmic order ceiling. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.FieldRankIndexOrderNumerics

theorem rank_le_log_index (q r m : ℕ) (hq : 2 ≤ q) (hindex : q^r ≤ m) :
    r ≤ Nat.log 2 m :=
  Nat.le_log_of_pow_le (by decide) ((Nat.pow_le_pow_left hq r).trans hindex)

theorem matrix_power_le_index_log_power (q r m : ℕ)
    (hq : 2 ≤ q) (hr : 2 ≤ r) (hindex : q^r ≤ m) :
    q^(2*(r+1)^2) ≤ m^(4*Nat.log 2 m+1) := by
  have hd : 2*(r+1)^2 ≤ r*(4*r+1) := by nlinarith
  have hlog := rank_le_log_index q r m hq hindex
  have hm : 1 ≤ m := (Nat.one_le_pow r q (by omega)).trans hindex
  calc
    q^(2*(r+1)^2) ≤ q^(r*(4*r+1)) := Nat.pow_le_pow_right (by omega) hd
    _ = (q^r)^(4*r+1) := pow_mul _ _ _
    _ ≤ m^(4*r+1) := Nat.pow_le_pow_left hindex _
    _ ≤ m^(4*Nat.log 2 m+1) := Nat.pow_le_pow_right hm (by omega)

end SymmetricSubgroupAsymptotics.FieldRankIndexOrderNumerics
