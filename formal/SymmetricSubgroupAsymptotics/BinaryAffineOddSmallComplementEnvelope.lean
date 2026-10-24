import SymmetricSubgroupAsymptotics.PrimeToSmallComplementEntropy
import SymmetricSubgroupAsymptotics.BinaryAffineDominantPrimeSwitchNumerics

/-! One uniform odd-dominant small-complement envelope. Its actual GL
coefficient is at most d-1, and the primary product is at least six.
All dimensions are paid by a quadratic induction; there is no prime,
exponent or group-row enumeration and no fitted scalar premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryAffineOddSmallComplementEnvelope
open BinaryAffineDominantPrimeSwitchNumerics

def budget (d : ℕ) : ℝ :=
  ((d : ℝ)-1)*((d : ℝ)+25)/15+
    ((d : ℝ)^2-(d : ℝ)+2)*(3/20)+1+(d : ℝ)/12

private theorem budget_le_two (d : ℕ) (hd : 2 ≤ d) : budget d ≤ (2 : ℝ)^d := by
  induction d,hd using Nat.le_induction with
  | base => norm_num [budget]
  | succ d hd ih =>
      have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
      have hx : 0 ≤ (d : ℝ)-2 := by linarith
      have heq : 2*budget d-budget (d+1) =
          (13*((d : ℝ)-2)^2+118*((d : ℝ)-2)+57)/60 := by
        simp only [budget,Nat.cast_add,Nat.cast_one]
        ring
      have hstep : budget (d+1) ≤ 2*budget d := by
        have hnonneg : 0 ≤ (13*((d : ℝ)-2)^2+118*((d : ℝ)-2)+57)/60 := by positivity
        linarith only [heq,hnonneg]
      calc
        budget (d+1) ≤ 2*budget d := hstep
        _ ≤ 2*(2 : ℝ)^d := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (2 : ℝ)^(d+1) := by rw [pow_succ]; ring

theorem budget_le (d : ℕ) (hd : 1 ≤ d) : budget d ≤ (2 : ℝ)^d := by
  by_cases hd1 : d = 1
  · subst d
    norm_num [budget]
  · exact budget_le_two d (by omega)

theorem envelope_le (q a d : ℕ) (hq : 3 ≤ q) (ha : 1 ≤ a)
    (hM : 64 ≤ q^a) (hd1 : 1 ≤ d) (hd6 : d ≤ 6)
    (C m : ℝ) (hm0 : 0 ≤ m) (hmC : m ≤ C) (hC : C ≤ (d : ℝ)^2)
    (hmPred : m ≤ (d : ℝ)-1) :
    (m*rate q a+(C-m+1)/(q : ℝ)^a)*
        Real.sqrt ((d : ℝ)+(a : ℝ)*Real.logb 2 (q : ℝ)+19) +
      Real.sqrt (1+(d : ℝ)/((a : ℝ)*Real.logb 2 (q : ℝ))) ≤ (2 : ℝ)^d := by
  let M := q^a
  let A := (a : ℝ)*Real.logb 2 (q : ℝ)
  let R := ((d : ℝ)+25)/15
  have hMR : (64 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hdR6 : (d : ℝ) ≤ 6 := by exact_mod_cast hd6
  have hlogM : Real.logb 2 (M : ℝ) = A := by
    simp only [M,A,Nat.cast_pow,Real.logb_pow]
  have hA6 : (6 : ℝ) ≤ A := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 64) hMR
    have heq : Real.logb 2 (64 : ℝ) = 6 := by
      rw [show (64 : ℝ) = 2^6 by norm_num,Real.logb_pow,
        Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one]
      norm_num
    simpa only [heq,hlogM] using hh
  have hprod := PrimeToSmallComplementEntropy.primary_product_ge_six q a hq ha hM
  have hprodR : (6 : ℝ) ≤ ((q : ℝ)-1)*a := by
    have hh : (6 : ℝ) ≤ (((q-1)*a : ℕ) : ℝ) := by exact_mod_cast hprod
    simpa only [Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ q),Nat.cast_one] using hh
  have hden : 0 < 3*((q : ℝ)-1)*a := by nlinarith only [hprodR]
  have hu0 : 0 ≤ rate q a := Real.sqrt_nonneg _
  have hu2 : (rate q a)^2 = 2/(3*((q : ℝ)-1)*a) :=
    Real.sq_sqrt (div_nonneg (by norm_num) hden.le)
  have husq : (rate q a)^2 ≤ 1/9 := by
    rw [hu2]
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hprodR]
  have hbase : (rate q a)^2*A ≤ 2/3 := by
    have hlog := logb_nat_le_sub_one q (by omega)
    have hh := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ a by positivity)
    dsimp only [A]
    rw [hu2,div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hh]
  have hrad0 : 0 ≤ (d : ℝ)+A+19 := by linarith
  have hprimary : rate q a*Real.sqrt ((d : ℝ)+A+19) ≤ R := by
    have hother := mul_le_mul_of_nonneg_right husq
      (show 0 ≤ (d : ℝ)+19 by positivity)
    have hsquare : (rate q a*Real.sqrt ((d : ℝ)+A+19))^2 ≤ ((d : ℝ)+25)/9 := by
      rw [mul_pow,Real.sq_sqrt hrad0]
      nlinarith only [hbase,hother]
    have hR0 : 0 ≤ R := by dsimp only [R]; positivity
    have hR : ((d : ℝ)+25)/9 ≤ R^2 := by
      have hh := mul_nonneg hd0 (show 0 ≤ (d : ℝ)+25 by positivity)
      dsimp only [R]
      nlinarith only [hh]
    exact (sq_le_sq₀ (mul_nonneg hu0 (Real.sqrt_nonneg _)) hR0).mp (hsquare.trans hR)
  have hratio : Real.sqrt ((d : ℝ)+A+19)/(M : ℝ) ≤ 3/20 := by
    have hlog := logb_nat_le_sub_one M (by omega)
    rw [hlogM] at hlog
    have hrad : (d : ℝ)+A+19 ≤ (M : ℝ)+24 := by linarith only [hlog,hdR6]
    have hquad := mul_le_mul_of_nonneg_right hMR hM0.le
    have hsqrt : Real.sqrt ((d : ℝ)+A+19) ≤ (3/20)*(M : ℝ) := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity,?_⟩
      nlinarith only [hrad,hquad,hMR]
    exact (div_le_iff₀ hM0).mpr hsqrt
  have hfirst : (m*rate q a+(C-m+1)/(M : ℝ))*Real.sqrt ((d : ℝ)+A+19) ≤
      m*R+(C-m+1)*(3/20) := by
    have hh := add_le_add (mul_le_mul_of_nonneg_left hprimary hm0)
      (mul_le_mul_of_nonneg_left hratio (show 0 ≤ C-m+1 by linarith))
    convert hh using 1
    ring
  have hcoeff : m*R+(C-m+1)*(3/20) ≤
      ((d : ℝ)-1)*R+((d : ℝ)^2-(d : ℝ)+2)*(3/20) := by
    have hR : 0 ≤ R-3/20 := by dsimp only [R]; linarith
    have hh := add_le_add (mul_le_mul_of_nonneg_right hmPred hR)
      (mul_le_mul_of_nonneg_right (add_le_add hC (le_rfl : (1 : ℝ) ≤ 1))
        (by norm_num : (0 : ℝ) ≤ 3/20))
    convert hh using 1 <;> ring
  have htop : Real.sqrt (1+(d : ℝ)/A) ≤ 1+(d : ℝ)/12 := by
    have hh := div_le_div_of_nonneg_left hd0 (by norm_num : (0 : ℝ) < 6) hA6
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith [sq_nonneg (d : ℝ)]
  have hsum := add_le_add (hfirst.trans hcoeff) htop
  have hbudget := budget_le d hd1
  dsimp only [budget] at hbudget
  simp only [M,Nat.cast_pow,A,R] at hsum
  linarith only [hsum,hbudget]

end SymmetricSubgroupAsymptotics.BinaryAffineOddSmallComplementEnvelope
