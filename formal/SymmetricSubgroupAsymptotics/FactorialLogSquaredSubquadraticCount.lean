import SymmetricSubgroupAsymptotics.GrowingMenuMassEntryCertificate
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-! Scalar conversion of a literal factorial/polylogarithmic count to the
exact all-width subquadratic menu-index interface. No group count premise
is proved or concealed by the scalar conversion. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology BigOperators Classical
namespace SymmetricSubgroupAsymptotics.FactorialLogSquaredSubquadraticCount

theorem factorial_logb_le (n : ℕ) (_hn : 2 ≤ n) :
    Real.logb 2 (n.factorial : ℝ) ≤ (n : ℝ)*Real.logb 2 (n : ℝ) := by
  have hp : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hpow : (n.factorial : ℝ) ≤ (n : ℝ)^n := by exact_mod_cast n.factorial_le_pow
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2) hp hpow
  simpa only [Real.logb_pow] using hh

theorem factorial_budget_bound (C n : ℕ) (hn : 2 ≤ n) :
    (n.factorial : ℝ)^((Nat.log 2 n+2)*C+(Nat.log 2 n)^2) ≤
      (2 : ℝ)^((3*(C : ℝ)+1)*(n : ℝ)*(Real.logb 2 (n : ℝ))^3) := by
  let L := Real.logb 2 (n : ℝ)
  let b := (Nat.log 2 n+2)*C+(Nat.log 2 n)^2
  have hL : 1 ≤ L := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
      (by norm_num : (0 : ℝ)<2) (by exact_mod_cast hn : (2 : ℝ)≤n)
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2)] using hh
  have hl : (Nat.log 2 n : ℝ) ≤ L := Real.natLog_le_logb n 2
  have hl0 : (0 : ℝ) ≤ Nat.log 2 n := by positivity
  have hc : (0 : ℝ) ≤ C := by positivity
  have hsq : (Nat.log 2 n : ℝ)^2 ≤ L^2 :=
    (sq_le_sq₀ hl0 (by linarith)).mpr hl
  have hlin : ((Nat.log 2 n : ℝ)+2)*(C : ℝ) ≤ (L+2)*(C : ℝ) :=
    mul_le_mul_of_nonneg_right (show (Nat.log 2 n : ℝ)+2 ≤ L+2 by linarith only [hl]) hc
  have hb : (b : ℝ) ≤ (3*(C : ℝ)+1)*L^2 := by
    dsimp only [b]
    push_cast
    nlinarith [mul_nonneg hc (show 0≤L^2-L by nlinarith),
      mul_nonneg hc (show 0≤L^2-1 by nlinarith)]
  have hf := factorial_logb_le n hn
  have hnl : 0 ≤ (n : ℝ)*L := mul_nonneg (by positivity) (by linarith)
  have he : (b : ℝ)*Real.logb 2 (n.factorial : ℝ) ≤
      (3*(C : ℝ)+1)*(n : ℝ)*L^3 := by
    calc
      _ ≤ (b : ℝ)*((n : ℝ)*L) := mul_le_mul_of_nonneg_left hf (by positivity)
      _ ≤ ((3*(C : ℝ)+1)*L^2)*((n : ℝ)*L) := mul_le_mul_of_nonneg_right hb hnl
      _ = _ := by ring
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ)<2)
    (by positivity : 0<(n.factorial : ℝ)^b)).mp
  simpa only [Real.logb_pow,L] using he

theorem factorial_budget_eventually (C : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,
      (n.factorial : ℝ)^((Nat.log 2 n+2)*C+(Nat.log 2 n)^2) ≤
        (2 : ℝ)^(ε*(n : ℝ)^2) := by
  have ht : Tendsto (fun n : ℕ =>
      (3*(C : ℝ)+1)*((Real.logb 2 (n : ℝ))^3/(n : ℝ))) atTop (𝓝 0) := by
    simpa only [one_mul,add_zero,mul_zero] using
      ((Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 0 3 one_ne_zero).comp
        tendsto_natCast_atTop_atTop).const_mul (3*(C : ℝ)+1)
  filter_upwards [ht.eventually (eventually_lt_nhds hε),eventually_ge_atTop 2] with n hs hn
  have hnp : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hsmall : (3*(C : ℝ)+1)*(Real.logb 2 (n : ℝ))^3 ≤ ε*(n : ℝ) :=
    ((div_lt_iff₀ hnp).mp (by simpa only [mul_div_assoc] using hs)).le
  have hexp : (3*(C : ℝ)+1)*(n : ℝ)*(Real.logb 2 (n : ℝ))^3 ≤ ε*(n : ℝ)^2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hsmall (le_of_lt hnp)]
  exact (factorial_budget_bound C n hn).trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)

theorem subquadratic_of_eventually {ι : ℕ → Type} [∀ n,Fintype (ι n)]
    (h : ∀ ε : ℝ,0<ε → ∀ᶠ n : ℕ in atTop,
      (Nat.card (ι n) : ℝ) ≤ (2 : ℝ)^(ε*(n : ℝ)^2)) :
    SubquadraticMenuIndexCount ι := by
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (h ε hε)
  let B : ℝ := 1+∑ n ∈ Finset.range N,(Nat.card (ι n) : ℝ)
  have hB : 1≤B := by
    have hs : 0 ≤ ∑ n ∈ Finset.range N,(Nat.card (ι n) : ℝ) := by positivity
    dsimp only [B]
    linarith
  refine ⟨B,by linarith,?_⟩
  intro n
  have hp : 1 ≤ (2 : ℝ)^(ε*(n : ℝ)^2) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg hε.le (sq_nonneg _))
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (le_mul_of_one_le_left (by positivity) hB)
  · have hmem : n ∈ Finset.range N := Finset.mem_range.mpr (by omega)
    have hc : (Nat.card (ι n) : ℝ) ≤ ∑ m ∈ Finset.range N,(Nat.card (ι m) : ℝ) :=
      Finset.single_le_sum (f := fun m => (Nat.card (ι m) : ℝ))
        (fun m _ => Nat.cast_nonneg _) hmem
    have hcB : (Nat.card (ι n) : ℝ) ≤ B := by dsimp only [B]; linarith
    exact hcB.trans (le_mul_of_one_le_right (by linarith : 0≤B) hp)

theorem subquadratic_of_factorial_budget {ι : ℕ → Type} [∀ n,Fintype (ι n)]
    (C : ℕ) (hcount : ∀ n : ℕ,2≤n →
      Nat.card (ι n) ≤ n.factorial^((Nat.log 2 n+2)*C+(Nat.log 2 n)^2)) :
    SubquadraticMenuIndexCount ι := by
  apply subquadratic_of_eventually
  intro ε hε
  filter_upwards [factorial_budget_eventually C ε hε,eventually_ge_atTop 2] with n hs hn
  have hc : (Nat.card (ι n) : ℝ) ≤
      (n.factorial : ℝ)^((Nat.log 2 n+2)*C+(Nat.log 2 n)^2) := by exact_mod_cast hcount n hn
  exact hc.trans hs

end SymmetricSubgroupAsymptotics.FactorialLogSquaredSubquadraticCount
