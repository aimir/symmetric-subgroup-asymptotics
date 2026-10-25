import SymmetricSubgroupAsymptotics.NonaffineLocalDegreeOrdinaryTailNumerics
import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate

/-! Real LOCAL-degree budgets for the uniform nonaffine block recurrence.
The top-degree normalization is separate; neither a group-rank inequality
nor a desired aggregate is an input here. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NonaffineLocalDegreeOrdinaryRealTail

private theorem four_pow_eq_square (m : ℕ) : (4 : ℝ)^m = ((2 : ℝ)^m)^2 := by
  calc
    (4 : ℝ)^m = ((2 : ℝ)^2)^m := by norm_num
    _ = (2 : ℝ)^(2*m) := (pow_mul _ _ _).symm
    _ = (2 : ℝ)^(m*2) := by rw [Nat.mul_comm]
    _ = ((2 : ℝ)^m)^2 := pow_mul _ _ _

private theorem dyadic_data (r : ℕ) (hr : 1024 ≤ r) :
    ∃ m : ℕ, 10 ≤ m ∧ (2 : ℝ)^m ≤ (r : ℝ) ∧
      Real.logb 2 (r : ℝ) ≤ (m : ℝ)+1 := by
  let m := Nat.log 2 r
  have hr0 : r ≠ 0 := by omega
  have hm : 10 ≤ m := Nat.le_log_of_pow_le (by decide : 1 < 2)
    (show 2^10 ≤ r by simpa only [show (2 : ℕ)^10 = 1024 by decide] using hr)
  have hp : (2 : ℝ)^m ≤ (r : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hr0
  have hh := IntegerLogSquareRootCeilingCertificate.log_upper r 1 (m+1)
    (by omega) (by decide)
    (by simpa only [pow_one] using (Nat.lt_pow_succ_log_self (by decide : 1 < 2) r).le)
  refine ⟨m,hm,hp,?_⟩
  simpa only [Nat.cast_add,Nat.cast_one,div_one] using hh

theorem multiple_factor_budget (r : ℕ) (hr : 1024 ≤ r) :
    (Real.sqrt (r : ℝ)+(Real.logb 2 (r : ℝ))^2+5*Real.logb 2 (r : ℝ)+3/2)*
        Real.sqrt (Real.logb 2 (r : ℝ)+1) ≤ (r : ℝ) := by
  obtain ⟨m,hm,hp,hLu⟩ := dyadic_data r hr
  let L := Real.logb 2 (r : ℝ)
  let u := (m : ℝ)+1
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hL : 0 ≤ L := Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ r by omega))
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hLu' : L ≤ u := hLu
  have hlinear : 9*(L+1) ≤ (r : ℝ) := by
    have hh0 : 9*((m : ℝ)+2) ≤ (2 : ℝ)^m := by
      exact_mod_cast NonaffineLocalDegreeOrdinaryTailNumerics.linear_budget m hm
    have hh : 9*(u+1) ≤ (2 : ℝ)^m := by
      convert hh0 using 1 <;> dsimp only [u] <;> ring
    nlinarith only [hLu',hh,hp]
  have hP : 0 ≤ 2*L^2+10*L+3 := by positivity
  have hU : 0 ≤ 2*u^2+10*u+3 := by positivity
  have hPU : 2*L^2+10*L+3 ≤ 2*u^2+10*u+3 := by
    nlinarith only [(sq_le_sq₀ hL hu).mpr hLu',hLu']
  have hpoly : 9*(L+1)*(2*L^2+10*L+3)^2 ≤ 16*(r : ℝ)^2 := by
    have hh0 : 9*((m : ℝ)+2)*(2*((m : ℝ)+1)^2+10*((m : ℝ)+1)+3)^2 ≤
        16*(4 : ℝ)^m := by
      exact_mod_cast NonaffineLocalDegreeOrdinaryTailNumerics.polynomial_budget m hm
    have hh : 9*(u+1)*(2*u^2+10*u+3)^2 ≤ 16*(4 : ℝ)^m := by
      convert hh0 using 1 <;> dsimp only [u] <;> ring
    have hprod := mul_le_mul (add_le_add hLu' (le_refl (1 : ℝ)))
      ((sq_le_sq₀ hP hU).mpr hPU) (sq_nonneg _) (by linarith only [hu] : 0 ≤ u+1)
    have hpow := (sq_le_sq₀ (by positivity : 0 ≤ (2 : ℝ)^m) hrR.le).mpr hp
    rw [four_pow_eq_square] at hh
    nlinarith only [hh,hprod,hpow]
  have hfirstSq : (Real.sqrt (r : ℝ)*Real.sqrt (L+1))^2 ≤ ((r : ℝ)/3)^2 := by
    rw [mul_pow,Real.sq_sqrt hrR.le,Real.sq_sqrt (by linarith only [hL] : 0 ≤ L+1)]
    nlinarith only [mul_le_mul_of_nonneg_right hlinear hrR.le]
  have hfirst : Real.sqrt (r : ℝ)*Real.sqrt (L+1) ≤ (r : ℝ)/3 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mp hfirstSq
  have hsecondSq : ((L^2+5*L+3/2)*Real.sqrt (L+1))^2 ≤ (2*(r : ℝ)/3)^2 := by
    rw [mul_pow,Real.sq_sqrt (by linarith only [hL] : 0 ≤ L+1)]
    nlinarith only [hpoly]
  have hsecond : (L^2+5*L+3/2)*Real.sqrt (L+1) ≤ 2*(r : ℝ)/3 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mp hsecondSq
  change (Real.sqrt (r : ℝ)+L^2+5*L+3/2)*Real.sqrt (L+1) ≤ (r : ℝ)
  nlinarith only [hfirst,hsecond]

/-- The actual one-factor outer-order term has a quarter-degree budget. -/
theorem one_factor_outer_budget (r : ℕ) (hr : 1024 ≤ r) :
    (2*Real.logb 2 (r : ℝ)+5)*Real.sqrt (Real.logb 2 (r : ℝ)+1) ≤ (r : ℝ)/4 := by
  obtain ⟨m,hm,hp,hLu⟩ := dyadic_data r hr
  let L := Real.logb 2 (r : ℝ)
  let u := (m : ℝ)+1
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hL : 0 ≤ L := Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ r by omega))
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hLu' : L ≤ u := hLu
  have hP : 0 ≤ 2*L+5 := by positivity
  have hU : 0 ≤ 2*u+5 := by positivity
  have hPU : 2*L+5 ≤ 2*u+5 := by linarith only [hLu']
  have hpoly : 16*(L+1)*(2*L+5)^2 ≤ (r : ℝ)^2 := by
    have hh0 : 16*((m : ℝ)+2)*(2*((m : ℝ)+1)+5)^2 ≤ (4 : ℝ)^m := by
      exact_mod_cast NonaffineLocalDegreeOrdinaryTailNumerics.cubic_budget m hm
    have hh : 16*(u+1)*(2*u+5)^2 ≤ (4 : ℝ)^m := by
      convert hh0 using 1 <;> dsimp only [u] <;> ring
    have hprod := mul_le_mul (add_le_add hLu' (le_refl (1 : ℝ)))
      ((sq_le_sq₀ hP hU).mpr hPU) (sq_nonneg _) (by linarith only [hu] : 0 ≤ u+1)
    have hpow := (sq_le_sq₀ (by positivity : 0 ≤ (2 : ℝ)^m) hrR.le).mpr hp
    rw [four_pow_eq_square] at hh
    nlinarith only [hh,hprod,hpow]
  have hs : ((2*L+5)*Real.sqrt (L+1))^2 ≤ ((r : ℝ)/4)^2 := by
    rw [mul_pow,Real.sq_sqrt (by linarith only [hL] : 0 ≤ L+1)]
    nlinarith only [hpoly]
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hs

end SymmetricSubgroupAsymptotics.NonaffineLocalDegreeOrdinaryRealTail
