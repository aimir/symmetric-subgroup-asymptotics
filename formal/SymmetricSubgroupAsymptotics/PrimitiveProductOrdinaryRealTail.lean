import SymmetricSubgroupAsymptotics.PrimitiveProductOrdinaryTailNumerics
import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate

/-! A real tail for the ordinary product-index recurrence. This is a
scalar result only; the actual simple factor, quotient, and outer-order
bound must still be supplied by an action installer. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveProductOrdinaryRealTail

private theorem four_pow_eq_square (m : ℕ) :
    (4 : ℝ)^m = ((2 : ℝ)^m)^2 := by
  calc
    (4 : ℝ)^m = ((2 : ℝ)^2)^m := by norm_num
    _ = (2 : ℝ)^(2*m) := (pow_mul _ _ _).symm
    _ = (2 : ℝ)^(m*2) := by rw [Nat.mul_comm]
    _ = ((2 : ℝ)^m)^2 := pow_mul _ _ _

theorem aggregate_le (n : ℕ) (hn : 1024 ≤ n) :
    2*Real.sqrt (n : ℝ)+(Real.logb 2 (n : ℝ))^2+
        5*Real.logb 2 (n : ℝ) ≤
      (n : ℝ)/Real.sqrt (Real.logb 2 (n : ℝ)) := by
  let m := Nat.log 2 n
  let L := Real.logb 2 (n : ℝ)
  let u := (m : ℝ)+1
  have hn0 : n ≠ 0 := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm : 10 ≤ m := Nat.le_log_of_pow_le (by decide : 1 < 2)
    (show 2^10 ≤ n by simpa only [show (2 : ℕ)^10 = 1024 by decide] using hn)
  have hp : (2 : ℝ)^m ≤ (n : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 hn0
  have hL : 0 < L := Real.logb_pos (by norm_num) (by exact_mod_cast (show 1 < n by omega))
  have hLu : L ≤ u := by
    have hh := IntegerLogSquareRootCeilingCertificate.log_upper n 1 (m+1)
      (by omega) (by decide)
      (by simpa only [pow_one] using
        (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).le)
    simpa only [L,u,Nat.cast_add,Nat.cast_one,div_one] using hh
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hlinear : 36*L ≤ (n : ℝ) := by
    have hh : 36*u ≤ (2 : ℝ)^m := by
      dsimp only [u]
      exact_mod_cast PrimitiveProductOrdinaryTailNumerics.linear_budget m hm
    exact (mul_le_mul_of_nonneg_left hLu (by norm_num : (0 : ℝ) ≤ 36)).trans
      (hh.trans hp)
  have hP : 0 ≤ L^2+5*L := by positivity
  have hU : 0 ≤ u^2+5*u := by positivity
  have hPU : L^2+5*L ≤ u^2+5*u := by
    have hh := (sq_le_sq₀ hL.le hu).mpr hLu
    nlinarith only [hh,hLu]
  have hpoly : 9*L*(L^2+5*L)^2 ≤ 4*(n : ℝ)^2 := by
    have hh : 9*u*(u^2+5*u)^2 ≤ 4*(4 : ℝ)^m := by
      dsimp only [u]
      exact_mod_cast PrimitiveProductOrdinaryTailNumerics.polynomial_budget m hm
    have hprod := mul_le_mul hLu ((sq_le_sq₀ hP hU).mpr hPU)
      (sq_nonneg (L^2+5*L)) hu
    have hpow := (sq_le_sq₀ (by positivity : 0 ≤ (2 : ℝ)^m) hnR.le).mpr hp
    rw [four_pow_eq_square] at hh
    nlinarith only [hprod,hh,hpow]
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hsSq : (Real.sqrt L)^2 = L := Real.sq_sqrt hL.le
  have hnSq : (Real.sqrt (n : ℝ))^2 = (n : ℝ) := Real.sq_sqrt hnR.le
  have hfirstSq : (6*Real.sqrt (n : ℝ)*Real.sqrt L)^2 ≤ (n : ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_right hlinear hnR.le
    calc
      _ = 36*(n : ℝ)*L := by rw [mul_pow,mul_pow,hnSq,hsSq]; ring
      _ ≤ (n : ℝ)^2 := by nlinarith only [hh]
  have hfirst : 6*Real.sqrt (n : ℝ)*Real.sqrt L ≤ (n : ℝ) :=
    (sq_le_sq₀ (by positivity) hnR.le).mp hfirstSq
  have hsecondSq : (3*(L^2+5*L)*Real.sqrt L)^2 ≤ (2*(n : ℝ))^2 := by
    calc
      _ = 9*L*(L^2+5*L)^2 := by rw [mul_pow,mul_pow,hsSq]; ring
      _ ≤ (2*(n : ℝ))^2 := by nlinarith only [hpoly]
  have hsecond : 3*(L^2+5*L)*Real.sqrt L ≤ 2*(n : ℝ) :=
    (sq_le_sq₀ (mul_nonneg (mul_nonneg (by norm_num) hP) hs.le)
      (by positivity)).mp hsecondSq
  change 2*Real.sqrt (n : ℝ)+L^2+5*L ≤ (n : ℝ)/Real.sqrt L
  apply (le_div_iff₀ hs).mpr
  nlinarith only [hfirst,hsecond]

end SymmetricSubgroupAsymptotics.PrimitiveProductOrdinaryRealTail
