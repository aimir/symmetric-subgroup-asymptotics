import SymmetricSubgroupAsymptotics.BinaryAffineDominantPrimeSwitchNumerics

/-! A uniform exponent128 primary margin for the sharper17/4 entropy.
All inequalities are proved without enumerating dimensions, primes,
exponents or group rows. The cubic exponential budget includes the
critical dimension-one seed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryAffineReducedDominantPrimeNumerics
open BinaryAffineDominantPrimeSwitchNumerics

theorem primary_switch_le (q a : ℕ) (hq : 2 ≤ q) (ha : 128 ≤ a)
    (d : ℝ) (hd0 : 0 ≤ d) :
    rate q a * Real.sqrt (d+(a : ℝ)*Real.logb 2 (q : ℝ)+(17/4)/(rate q a)) ≤
      (d+379)/384 := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have haR : (128 : ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < a := by linarith
  have hprod : (128 : ℝ) ≤ ((q : ℝ)-1)*a := by
    have hh := mul_le_mul (by linarith : (1 : ℝ) ≤ (q : ℝ)-1) haR
      (by norm_num : (0 : ℝ) ≤ 128) (by linarith : (0 : ℝ) ≤ (q : ℝ)-1)
    simpa only [one_mul] using hh
  have hden : 0 < 3*((q : ℝ)-1)*a :=
    mul_pos (mul_pos (by norm_num) (by linarith)) ha0
  have hden_large : (384 : ℝ) ≤ 3*((q : ℝ)-1)*a := by nlinarith only [hprod]
  have hu : 0 < rate q a := Real.sqrt_pos.mpr (div_pos (by norm_num) hden)
  have hu2 : (rate q a)^2 = 2/(3*((q : ℝ)-1)*a) :=
    Real.sq_sqrt (div_nonneg (by norm_num) hden.le)
  have husq : (rate q a)^2 ≤ 1/192 := by
    rw [hu2]
    exact (div_le_iff₀ hden).mpr (by nlinarith only [hden_large])
  have hule : rate q a ≤ 13/180 :=
    (sq_le_sq₀ hu.le (by norm_num : (0 : ℝ) ≤ 13/180)).mp (by nlinarith only [husq])
  have hlog := logb_nat_le_sub_one q hq
  have hlog0 : 0 ≤ Real.logb 2 (q : ℝ) :=
    (Real.logb_pos (by norm_num : (1 : ℝ) < 2) (by linarith : (1 : ℝ) < q)).le
  have hbase : (rate q a)^2*((a : ℝ)*Real.logb 2 (q : ℝ)) ≤ 2/3 := by
    rw [hu2,div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    have hh := mul_le_mul_of_nonneg_left hlog ha0.le
    nlinarith only [hh]
  have hdim : (rate q a)^2*d ≤ d/192 := by
    simpa only [div_eq_mul_inv,one_mul,mul_comm] using mul_le_mul_of_nonneg_right husq hd0
  have hrad : 0 ≤ d+(a : ℝ)*Real.logb 2 (q : ℝ)+(17/4)/(rate q a) :=
    add_nonneg (add_nonneg hd0 (mul_nonneg ha0.le hlog0))
      (div_nonneg (by norm_num) hu.le)
  have hexpand :
      (rate q a * Real.sqrt (d+(a : ℝ)*Real.logb 2 (q : ℝ)+(17/4)/(rate q a)))^2 =
        (rate q a)^2*d+(rate q a)^2*((a : ℝ)*Real.logb 2 (q : ℝ))+(17/4)*rate q a := by
    rw [mul_pow,Real.sq_sqrt hrad]
    field_simp [hu.ne'] <;> ring
  apply (sq_le_sq₀ (mul_nonneg hu.le (Real.sqrt_nonneg _))
    (by positivity : (0 : ℝ) ≤ (d+379)/384)).mp
  rw [hexpand]
  nlinarith only [hdim,hbase,hule,sq_nonneg (d-5)]

theorem cubic_budget (d : ℕ) (hd : 1 ≤ d) :
    4*d*(d+1)*(d+379)+12*d+3075 ≤ 3072*2^d := by
  induction d,hd using Nat.le_induction with
  | base => decide
  | succ d hd ih =>
    have hstep : 4*(d+1)*(d+2)*(d+380)+12*(d+1)+3075 ≤
        2*(4*d*(d+1)*(d+379)+12*d+3075) := by
      obtain ⟨k,rfl⟩ : ∃ k : ℕ, d = k+1 := ⟨d-1,by omega⟩
      nlinarith only [Nat.zero_le (k^3),Nat.zero_le (k^2),Nat.zero_le k]
    calc
      _ ≤ 2*(4*d*(d+1)*(d+379)+12*d+3075) := by simpa only [Nat.add_assoc] using hstep
      _ ≤ 2*(3072*2^d) := Nat.mul_le_mul_left _ ih
      _ = 3072*2^(d+1) := by rw [pow_succ]; ring

theorem aggregate_margin (d : ℕ) (hd : 1 ≤ d) :
    ((d+d*(d-1)/2 : ℕ) : ℝ)*((d : ℝ)+379)/384+1+(d : ℝ)/256+1/1024 ≤
      (2 : ℝ)^d := by
  have hdiv := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self d)
  have hsub : d-1+1 = d := by omega
  have hmul := congrArg (fun x : ℕ => d*x) hsub
  have htri : 2*(d+d*(d-1)/2) = d*(d+1) := by nlinarith only [hdiv,hmul]
  have htriR : (2 : ℝ)*((d+d*(d-1)/2 : ℕ) : ℝ) = (d : ℝ)*((d : ℝ)+1) := by
    exact_mod_cast htri
  have hmult := congrArg (fun x : ℝ => x*((d : ℝ)+379)) htriR
  have hbudget : 4*(d : ℝ)*((d : ℝ)+1)*((d : ℝ)+379)+12*(d : ℝ)+3075 ≤
      3072*(2 : ℝ)^d := by exact_mod_cast cubic_budget d hd
  nlinarith only [hbudget,hmult]

end SymmetricSubgroupAsymptotics.BinaryAffineReducedDominantPrimeNumerics
