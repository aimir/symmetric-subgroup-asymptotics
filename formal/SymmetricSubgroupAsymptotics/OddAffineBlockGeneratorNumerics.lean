import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Integer rounding for three actual odd-affine block layers. The top
may use its rounded smaller-degree bound, including the S3 exception. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.OddAffineBlockGeneratorNumerics

theorem two_mul_add_one_le_pow (p d : ℕ) (hp : 3 ≤ p) (hd : 1 ≤ d) :
    2*d+1 ≤ p^d := by
  induction d with
  | zero => omega
  | succ d ih =>
      by_cases hz : d = 0
      · subst d
        simpa only [Nat.zero_add,pow_one] using hp
      · have hrec := ih (by omega)
        rw [pow_succ]
        have hm := Nat.mul_le_mul hrec hp
        nlinarith

theorem two_mul_add_two_le_pow (p d : ℕ) (hp : 3 ≤ p) (hd : 1 ≤ d)
    (hfive : 5 ≤ p^d) : 2*d+2 ≤ p^d := by
  cases d with
  | zero => omega
  | succ d =>
      by_cases hz : d = 0
      · subst d
        have hp5 : 5 ≤ p := by simpa only [Nat.zero_add,pow_one] using hfive
        simpa only [Nat.zero_add,pow_one] using (show 4 ≤ p from by omega)
      · have hdpos : 1 ≤ d := by omega
        have hrec := two_mul_add_one_le_pow p d hp hdpos
        rw [pow_succ]
        have hm := Nat.mul_le_mul hrec hp
        nlinarith

/-- A rounded top bound plus the actual binary and d-dimensional
translation layers fits the sharp half-degree budget. -/
theorem half_degree_of_three_layers (q d t g a b c y : ℕ)
    (hq : 2*d+2 ≤ q) (ht : 2 ≤ t)
    (hpoints : 2*y ≤ (q-1)*t) (htop : 2*a ≤ y+1)
    (hsign : b ≤ t/2) (htranslation : c ≤ d*(t/2))
    (hgroup : g ≤ a+b+c) : 2*g ≤ q*t := by
  have hfloor : 2*(t/2) ≤ t := Nat.mul_div_le _ _
  have hcost : b+c ≤ (d+1)*(t/2) := by nlinarith
  have hcost4 : 4*(b+c) ≤ 2*(d+1)*t := by
    have hm := Nat.mul_le_mul_left (2*(d+1)) hfloor
    nlinarith
  have htotal : 4*g ≤ (q-1)*t+2+2*(d+1)*t := by nlinarith
  have hqt := Nat.mul_le_mul_right t hq
  have hsum : (q-1)*t+t = q*t := by
    calc
      (q-1)*t+t = ((q-1)+1)*t := by ring
      _ = q*t := by rw [Nat.sub_add_cancel (by omega)]
  nlinarith

end SymmetricSubgroupAsymptotics.OddAffineBlockGeneratorNumerics
