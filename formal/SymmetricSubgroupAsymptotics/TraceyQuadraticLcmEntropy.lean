import SymmetricSubgroupAsymptotics.ChebyshevThreeQuarterLogBound
import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate

/-! A quadratic complementary entropy with coefficient1/3. The existing
proved linear Chebyshev estimate pays every v>=13; the thirteen smaller
integers use only (lcm(1,...,v))^3 <=2^(v^2). This is scalar arithmetic,
not a group/action census or a new published input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TraceyQuadraticLcmEntropy

private theorem small_lcm_cube : ∀ v : Fin 13,
    (Nat.lcmUpto (v : ℕ))^3 ≤ 2^((v : ℕ)^2) := by
  decide +kernel

theorem log_lcmUpto_le_third_square (v : ℕ) :
    Real.logb 2 (Nat.lcmUpto v : ℝ) ≤ (v : ℝ)^2/3 := by
  by_cases hv : 13 ≤ v
  · have hh := ChebyshevThreeQuarterLogBound.log_lcmUpto_le_seventeen_quarters_mul v
    have hvR : (13 : ℝ) ≤ v := by exact_mod_cast hv
    have hprod : 0 ≤ (v : ℝ)*((v : ℝ)-51/4) :=
      mul_nonneg (by positivity) (by linarith only [hvR])
    exact hh.trans (by nlinarith only [hprod])
  · have hc : (Nat.lcmUpto v)^3 ≤ 2^(v^2) := small_lcm_cube ⟨v,by omega⟩
    have hh := IntegerLogSquareRootCeilingCertificate.log_upper (Nat.lcmUpto v) 3 (v^2)
      (Nat.lcmUpto_pos v) (by decide) hc
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh

theorem log_budget (p s v : ℕ) (hp : 1 ≤ p) (hs : s ≠ 0) (hv : 1 ≤ v)
    (hpower : ∀ q ∈ s.primeFactors, q ≠ p → q^s.factorization q ≤ v) :
    Real.logb 2 (s : ℝ) ≤ (((p-1)*s.factorization p : ℕ) : ℝ)+(v : ℝ)^2/3 := by
  have hdeg := TraceyElementarySharperLogBudget.degree_le_primary_mul_lcm p s v hs hv hpower
  have hdegR : (s : ℝ) ≤ (p : ℝ)^s.factorization p*(Nat.lcmUpto v : ℝ) := by
    exact_mod_cast hdeg
  have hpbound : p ≤ 2^(p-1) := by
    have hh := TraceyElementaryLogBudget.succ_le_two_pow (p-1)
    omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hpboundR : (p : ℝ) ≤ (2 : ℝ)^(p-1) := by exact_mod_cast hpbound
  have hlogp := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hpR hpboundR
  have hlogp' : Real.logb 2 (p : ℝ) ≤ ((p-1 : ℕ) : ℝ) := by
    simpa only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one]
      using hlogp
  have hsR : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hvR : (0 : ℝ) < Nat.lcmUpto v := by exact_mod_cast Nat.lcmUpto_pos v
  calc
    Real.logb 2 (s : ℝ) ≤
        Real.logb 2 ((p : ℝ)^s.factorization p*(Nat.lcmUpto v : ℝ)) :=
      Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hsR hdegR
    _ = (s.factorization p : ℝ)*Real.logb 2 (p : ℝ)+
        Real.logb 2 (Nat.lcmUpto v : ℝ) := by
      rw [Real.logb_mul (pow_ne_zero _ hpR.ne') hvR.ne',Real.logb_pow]
    _ ≤ (s.factorization p : ℝ)*((p-1 : ℕ) : ℝ)+(v : ℝ)^2/3 :=
      add_le_add (mul_le_mul_of_nonneg_left hlogp' (by positivity))
        (log_lcmUpto_le_third_square v)
    _ = (((p-1)*s.factorization p : ℕ) : ℝ)+(v : ℝ)^2/3 := by
      push_cast
      ring

end SymmetricSubgroupAsymptotics.TraceyQuadraticLcmEntropy
