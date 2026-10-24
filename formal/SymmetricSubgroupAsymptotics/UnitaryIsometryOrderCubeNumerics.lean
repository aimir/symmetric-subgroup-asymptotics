import SymmetricSubgroupAsymptotics.QuadraticRankOrderCubeNumerics

/-! A common field/rank tail for the proved isometry order bound.
Only small scalar seeds are evaluated; no action or group census occurs. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.UnitaryIsometryOrderCubeNumerics
open QuadraticRankOrderCubeNumerics

def exponent (r : ℕ) : ℕ := (r+1)*(r+3)

def Capacity (q r : ℕ) : Prop :=
  8 ≤ q ∨ (4 ≤ q ∧ 3 ≤ r) ∨ (3 ≤ q ∧ 4 ≤ r) ∨ 7 ≤ r

private theorem exponent_double (r : ℕ) (hr : 2 ≤ r) :
    exponent (r+1) ≤ 2*exponent r := by
  unfold exponent
  nlinarith

private theorem large (q r : ℕ) (hq : 8 ≤ q) (hr : 2 ≤ r) :
    q^(3*exponent r) ≤ 5^(q^r-1) :=
  rank_tail q (by omega) exponent 2 exponent_double
    (field_tail 8 2 15 7 (by decide) (by decide) (by decide) (by decide) q hq) r hr

private theorem medium (q r : ℕ) (hq : 4 ≤ q) (hr : 3 ≤ r) :
    q^(3*exponent r) ≤ 5^(q^r-1) :=
  rank_tail q (by omega) exponent 3 (fun r hr => exponent_double r (by omega))
    (field_tail 4 3 24 12 (by decide) (by decide) (by decide) (by decide) q hq) r hr

private theorem three (q r : ℕ) (hq : 3 ≤ q) (hr : 4 ≤ r) :
    q^(3*exponent r) ≤ 5^(q^r-1) := by
  by_cases he : q=3
  · subst q
    exact rank_tail 3 (by decide) exponent 4 (fun r hr => exponent_double r (by omega))
      (by decide) r hr
  · exact medium q r (by omega) (by omega)

theorem order_cube (q r : ℕ) (hq : 2 ≤ q) (hr : 2 ≤ r) (hc : Capacity q r) :
    q^(3*exponent r) ≤ 5^(q^r-1) := by
  rcases hc with h | ⟨h,h'⟩ | ⟨h,h'⟩ | h
  · exact large q r h hr
  · exact medium q r h h'
  · exact three q r h h'
  · by_cases he : q=2
    · subst q
      exact rank_tail 2 (by decide) exponent 7 (fun r hr => exponent_double r (by omega))
        (by decide) r h
    · exact three q r (by omega) (by omega)

theorem root_power_ge (q r : ℕ) (hq : 2 ≤ q) (hr : 2 ≤ r) (hc : Capacity q r) :
    32 ≤ q^r := by
  rcases hc with h | ⟨h,h'⟩ | ⟨h,h'⟩ | h
  · exact (by decide : 32 ≤ 8^2).trans
      ((Nat.pow_le_pow_left h 2).trans (Nat.pow_le_pow_right (by omega) hr))
  · exact (by decide : 32 ≤ 4^3).trans
      ((Nat.pow_le_pow_left h 3).trans (Nat.pow_le_pow_right (by omega) h'))
  · exact (by decide : 32 ≤ 3^4).trans
      ((Nat.pow_le_pow_left h 4).trans (Nat.pow_le_pow_right (by omega) h'))
  · exact (by decide : 32 ≤ 2^7).trans
      ((Nat.pow_le_pow_left hq 7).trans (Nat.pow_le_pow_right (by omega) h))

theorem small_parameters_of_not_capacity (q r : ℕ) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hc : ¬Capacity q r) :
    (r=2 ∧ q≤7) ∨ (r=3 ∧ q≤3) ∨ (4≤r ∧ r≤6 ∧ q=2) := by
  unfold Capacity at hc
  omega

end SymmetricSubgroupAsymptotics.UnitaryIsometryOrderCubeNumerics
