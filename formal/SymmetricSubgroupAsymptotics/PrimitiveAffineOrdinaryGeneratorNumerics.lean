import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Log
import Lean.Elab.Tactic.Omega

/-! Uniform parameter tails for the ordinary affine generator bound.
The seven-case uses 7≤2³; all other bases use p≤2^(p−1). -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineOrdinaryGeneratorNumerics

def exponentBudget (p : ℕ) : ℕ := if p=7 then 3 else p-1

theorem power_exponentBudget (p : ℕ) (hp : 0<p) : p≤2^(exponentBudget p) := by
  by_cases h:p=7
  · subst p; norm_num [exponentBudget]
  · rw [exponentBudget,if_neg h]
    have hh := (p-1).lt_two_pow_self
    omega

/-- These are infinite parameter ranges, not a finite-action catalogue. -/
def UniformTail (p d : ℕ) : Prop :=
  (p=2 ∧ 7≤d) ∨ (p=3 ∧ 4≤d) ∨ (5≤p ∧ 3≤d) ∨ (7≤p ∧ 2≤d)

private theorem quadratic_step (p b d : ℕ) (hp : 1≤p)
    (hsq : (d+1)^2≤p*d^2) :
    2*(b*(d+1)^2+1)≤p*(2*(b*d^2+1)) := by
  calc
    2*(b*(d+1)^2+1)≤2*(b*(p*d^2)+p) :=
      Nat.mul_le_mul_left 2 (Nat.add_le_add (Nat.mul_le_mul_left b hsq) hp)
    _=p*(2*(b*d^2+1)) := by ring

private theorem quadratic_tail (p b d₀ : ℕ)
    (hp : 1≤p) (hbase : 2*(b*d₀^2+1)≤p^d₀)
    (hstep : ∀d, d₀≤d→(d+1)^2≤p*d^2) :
    ∀d,d₀≤d→2*(b*d^2+1)≤p^d := by
  intro d hd
  induction d,hd using Nat.le_induction with
  | base => exact hbase
  | succ d hd ih =>
      calc
        2*(b*(d+1)^2+1)≤p*(2*(b*d^2+1)) := quadratic_step p b d hp (hstep d hd)
        _≤p*p^d := Nat.mul_le_mul_left p ih
        _=p^(d+1) := by rw [pow_succ,Nat.mul_comm]

private theorem square_step_two (d : ℕ) (hd : 3≤d) : (d+1)^2≤2*d^2 := by
  have hh := Nat.mul_le_mul_right d hd
  nlinarith

private theorem square_step_three (p d : ℕ) (hp : 3≤p) (hd : 2≤d) :
    (d+1)^2≤p*d^2 := by
  have hh := Nat.mul_le_mul_right d hd
  have h3 : (d+1)^2≤3*d^2 := by nlinarith
  exact h3.trans (Nat.mul_le_mul_right (d^2) hp)

private theorem binary_tail (d : ℕ) (hd : 7≤d) : 2*(d^2+1)≤2^d := by
  simpa only [one_mul] using quadratic_tail 2 1 7 (by decide) (by norm_num)
    (fun k hk=>square_step_two k (by omega)) d hd

private theorem ternary_tail (d : ℕ) (hd : 4≤d) : 2*(2*d^2+1)≤3^d :=
  quadratic_tail 3 2 4 (by decide) (by norm_num)
    (fun k hk=>square_step_three 3 k (by decide) (by omega)) d hd

private theorem ge_five_tail (p d : ℕ) (hp : 5≤p) (hd : 3≤d) :
    2*((p-1)*d^2+1)≤p^d := by
  have hbase : 2*((p-1)*3^2+1)≤p^3 := by
    have hpred : p-1+1=p := Nat.sub_add_cancel (by omega)
    have hp2 : 25≤p*p := Nat.mul_le_mul hp hp
    have hp3 : 25*p≤p*p*p := Nat.mul_le_mul_right p hp2
    norm_num only [pow_succ,pow_zero,mul_one]
    nlinarith
  exact quadratic_tail p (p-1) 3 (by omega) hbase
    (fun k hk=>square_step_three p k (by omega) (by omega)) d hd

private theorem ge_eight_tail (p d : ℕ) (hp : 8≤p) (hd : 2≤d) :
    2*((p-1)*d^2+1)≤p^d := by
  have hbase : 2*((p-1)*2^2+1)≤p^2 := by
    have hpred : p-1+1=p := Nat.sub_add_cancel (by omega)
    have hp2 : 8*p≤p*p := Nat.mul_le_mul_right p hp
    norm_num only [pow_succ,pow_zero,mul_one]
    nlinarith
  exact quadratic_tail p (p-1) 2 (by omega) hbase
    (fun k hk=>square_step_three p k (by omega) (by omega)) d hd

private theorem seven_tail (d : ℕ) (hd : 2≤d) : 2*(3*d^2+1)≤7^d :=
  quadratic_tail 7 3 2 (by decide) (by norm_num)
    (fun k hk=>square_step_three 7 k (by decide) hk) d hd

theorem half_degree_budget (p d : ℕ) (h : UniformTail p d) :
    2*(exponentBudget p*d^2+1)≤p^d := by
  by_cases hp7:p=7
  · subst p
    have hd : 2≤d := by rcases h with ⟨h,_⟩|⟨h,_⟩|⟨_,h⟩|⟨_,h⟩ <;> omega
    simpa only [exponentBudget,if_pos rfl] using seven_tail d hd
  · rw [exponentBudget,if_neg hp7]
    rcases h with ⟨rfl,hd⟩|⟨rfl,hd⟩|⟨hp,hd⟩|⟨hp,hd⟩
    · simpa only [Nat.reduceSub,one_mul] using binary_tail d hd
    · simpa only [Nat.reduceSub] using ternary_tail d hd
    · exact ge_five_tail p d hp hd
    · exact ge_eight_tail p d (by omega) hd

end SymmetricSubgroupAsymptotics.PrimitiveAffineOrdinaryGeneratorNumerics
