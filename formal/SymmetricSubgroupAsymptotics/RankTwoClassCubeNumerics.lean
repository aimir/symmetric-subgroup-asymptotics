import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! A uniform numerical class budget for the original rank-two A branch.
The finite-field gcd is retained in the input, and the exponential tail
is proved by one polynomial induction, not by field enumeration. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.RankTwoClassCubeNumerics

theorem twice_exponent_le_prime_power (p e:ℕ) (hp:2≤p) (he:0<e) : 2*e≤p^e := by
  have hh : ∀a:ℕ,0<a→2*a≤2^a := by
    intro a
    induction a with
    | zero=>omega
    | succ a ih=>
      intro _
      by_cases ha:a=0
      · subst a
        decide
      · have hi:=ih (by omega)
        have ha1:1≤a := by omega
        rw [pow_succ]
        nlinarith
  exact (hh e he).trans (Nat.pow_le_pow_left hp e)

private theorem polynomial_le_binary (q:ℕ) (hq:4≤q) :
    9*q^2*(q+2)≤2^(2*q+2) := by
  induction q,hq using Nat.le_induction with
  | base=>decide
  | succ q hq ih=>
    have hq2 : 2*q≤q^2 := by nlinarith
    have hq3 : 2*q^2≤q^3 := by
      have h:=Nat.mul_le_mul_left (q^2) (show 2≤q by omega)
      nlinarith
    have hstep : 9*(q+1)^2*((q+1)+2)≤4*(9*q^2*(q+2)) := by nlinarith
    calc
      _ ≤ 4*(9*q^2*(q+2)) := hstep
      _ ≤ 4*2^(2*q+2) := Nat.mul_le_mul_left _ ih
      _ = 2^(2*(q+1)+2) := by
        have he : 2*(q+1)+2=(2*q+2)+2 := by omega
        rw [he,pow_add]
        ring

theorem cubic_budget_of_four_le (q f g:ℕ) (hq:4≤q) (hf:2*f≤q) (hg:g≤3) :
    ((g*(q^2+2*q))*(2*g*f))^3≤5^(q^2-1) := by
  have hprod : (g*(q^2+2*q))*(2*g*f) ≤ 9*q^2*(q+2) := by
    calc
      _ ≤ (3*(q^2+2*q))*(2*3*f) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ hg)
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hg))
      _ = (9*q*(q+2))*(2*f) := by ring
      _ ≤ (9*q*(q+2))*q := Nat.mul_le_mul_left _ hf
      _ = _ := by ring
  have hexp : (2*q+2)*3 ≤ 2*(q^2-1) := by
    have hsq : 3*q+4≤q^2 := by nlinarith
    omega
  calc
    _ ≤ (2^(2*q+2))^3 := Nat.pow_le_pow_left (hprod.trans (polynomial_le_binary q hq)) 3
    _ = 2^((2*q+2)*3) := (pow_mul _ _ _).symm
    _ ≤ 2^(2*(q^2-1)) := Nat.pow_le_pow_right (by decide) hexp
    _ = (2^2)^(q^2-1) := pow_mul _ _ _
    _ ≤ 5^(q^2-1) := Nat.pow_le_pow_left (by decide) _

end SymmetricSubgroupAsymptotics.RankTwoClassCubeNumerics
