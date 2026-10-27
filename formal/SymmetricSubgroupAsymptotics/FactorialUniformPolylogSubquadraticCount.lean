import SymmetricSubgroupAsymptotics.FactorialLogSquaredSubquadraticCount

/-! A coefficient on the quadratic logarithmic tuple budget is harmless
for the exact weak subquadratic menu interface. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace SymmetricSubgroupAsymptotics.FactorialUniformPolylogSubquadraticCount
open FactorialLogSquaredSubquadraticCount

theorem factorial_budget_bound (A n : ℕ) (hn : 2≤n) :
    (n.factorial : ℝ)^(A*(Nat.log 2 n+2)^2) ≤
      (2 : ℝ)^((9*(A : ℝ))*(n : ℝ)*(Real.logb 2 (n : ℝ))^3) := by
  let L := Real.logb 2 (n : ℝ)
  let b := A*(Nat.log 2 n+2)^2
  have hL : 1≤L := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
      (by norm_num : (0 : ℝ)<2) (by exact_mod_cast hn : (2 : ℝ)≤n)
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2)] using hh
  have hl : (Nat.log 2 n : ℝ)≤L := Real.natLog_le_logb n 2
  have hl0 : (0 : ℝ)≤Nat.log 2 n := by positivity
  have hc : (0 : ℝ)≤A := by positivity
  have hs : ((Nat.log 2 n : ℝ)+2)^2≤(3*L)^2 :=
    (sq_le_sq₀ (by positivity) (by linarith)).mpr (by linarith)
  have hb : (b : ℝ)≤9*(A : ℝ)*L^2 := by
    dsimp only [b]
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_left hs hc]
  have hf := factorial_logb_le n hn
  have hnl : 0≤(n : ℝ)*L := mul_nonneg (by positivity) (by linarith)
  have he : (b : ℝ)*Real.logb 2 (n.factorial : ℝ) ≤
      (9*(A : ℝ))*(n : ℝ)*L^3 := by
    calc
      _ ≤ (b : ℝ)*((n : ℝ)*L) := mul_le_mul_of_nonneg_left hf (by positivity)
      _ ≤ (9*(A : ℝ)*L^2)*((n : ℝ)*L) := mul_le_mul_of_nonneg_right hb hnl
      _ = _ := by ring
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ)<2)
    (by positivity : 0<(n.factorial : ℝ)^b)).mp
  simpa only [Real.logb_pow,L] using he

theorem factorial_budget_eventually (A : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,
      (n.factorial : ℝ)^(A*(Nat.log 2 n+2)^2) ≤ (2 : ℝ)^(ε*(n : ℝ)^2) := by
  have ht : Tendsto (fun n : ℕ =>
      (9*(A : ℝ))*((Real.logb 2 (n : ℝ))^3/(n : ℝ))) atTop (𝓝 0) := by
    simpa only [one_mul,add_zero,mul_zero] using
      ((Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 0 3 one_ne_zero).comp
        tendsto_natCast_atTop_atTop).const_mul (9*(A : ℝ))
  filter_upwards [ht.eventually (eventually_lt_nhds hε),eventually_ge_atTop 2] with n hs hn
  have hnp : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hsmall : (9*(A : ℝ))*(Real.logb 2 (n : ℝ))^3 ≤ ε*(n : ℝ) :=
    ((div_lt_iff₀ hnp).mp (by simpa only [mul_div_assoc] using hs)).le
  have hexp : (9*(A : ℝ))*(n : ℝ)*(Real.logb 2 (n : ℝ))^3 ≤ ε*(n : ℝ)^2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hsmall (le_of_lt hnp)]
  exact (factorial_budget_bound A n hn).trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)

theorem subquadratic_of_factorial_budget {ι : ℕ → Type} [∀ n,Fintype (ι n)]
    (A : ℕ) (hcount : ∀ n : ℕ,2≤n →
      Nat.card (ι n)≤n.factorial^(A*(Nat.log 2 n+2)^2)) :
    SubquadraticMenuIndexCount ι := by
  apply subquadratic_of_eventually
  intro ε hε
  filter_upwards [factorial_budget_eventually A ε hε,eventually_ge_atTop 2] with n hs hn
  have hc : (Nat.card (ι n) : ℝ)≤(n.factorial : ℝ)^(A*(Nat.log 2 n+2)^2) := by
    exact_mod_cast hcount n hn
  exact hc.trans hs

end SymmetricSubgroupAsymptotics.FactorialUniformPolylogSubquadraticCount
