import SymmetricSubgroupAsymptotics.TraceyCoarseCeilingMonotonicity
import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate
import Mathlib.Tactic.IntervalCases

/-! Generic field-rank product and degree-band arithmetic for literal
unitary Sylow heads. These are scalar parameter inequalities, not finite
action rows or supplied generator certificates. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.UnitaryBoundedPrimitiveOrdinaryNumerics
open IntegerLogSquareRootCeilingCertificate

theorem product_bound (p f r n m : ℕ) (hp : 2 ≤ p)
    (hdegree : (p^f)^r ≤ n) (hn : n < 2^(m+1)) : f*r ≤ m := by
  have hpow : 2^(f*r) ≤ n :=
    (Nat.pow_le_pow_left hp (f*r)).trans (by simpa only [pow_mul] using hdegree)
  have hh : 2^(f*r) < 2^(m+1) := hpow.trans_lt hn
  have he : f*r < m+1 := (Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hh
  omega

theorem head_bound (f r m : ℕ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hfr : f*r ≤ m) :
    f*(r*(r+1)/2)+1 ≤ m*(m+1)/2+1 := by
  have hrm : r ≤ m := (Nat.le_mul_of_pos_left r hf).trans hfr
  have hd : 2*(r*(r+1)/2) ≤ r*(r+1) := Nat.mul_div_le _ _
  have hfd := Nat.mul_le_mul_left f hd
  have hproduct := Nat.mul_le_mul hfr (show r+1 ≤ m+1 by omega)
  have hh : 2*(f*(r*(r+1)/2)) ≤ m*(m+1) := by nlinarith only [hfd,hproduct]
  omega

theorem small_product_head (f r : ℕ) (hf : 1 ≤ f) (hr : 2 ≤ r)
    (hr4 : r ≤ 4) (hfr : f*r ≤ 5) : f*(r*(r+1)/2)+1 ≤ 11 := by
  interval_cases r <;> norm_num at * <;> omega

theorem outer_size_bound (f r m : ℕ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hfr : f*r ≤ m) :
    2*f*(r+1) ≤ 4*m := by
  have hfm : f ≤ m := (Nat.le_mul_of_pos_right f hr).trans hfr
  nlinarith only [hfm,hfr]

private theorem lower_at (n lo c u : ℕ) (hlo : 2 ≤ lo) (hln : lo ≤ n)
    (hpow : lo ≤ 2^u) (hc : 1 ≤ c) (hsquare : (c-1)^2*u < lo^2) :
    c ≤ traceyPermutationGeneratorCeiling n := by
  have hb : c ≤ traceyPermutationGeneratorCeiling lo := by
    exact le_ceil_of_square lo 1 u c hlo (by decide) hc
      (by simpa only [Nat.pow_one] using hpow) (by simpa only [Nat.one_mul] using hsquare)
  exact hb.trans (TraceyCoarseCeilingMonotonicity.ceiling_mono hlo hln)

theorem band_ceiling (n H : ℕ)
    (h : (32 ≤ n ∧ H ≤ 15) ∨ (64 ≤ n ∧ H ≤ 26) ∨
      (128 ≤ n ∧ H ≤ 33) ∨ (256 ≤ n ∧ H ≤ 51)) :
    H ≤ traceyPermutationGeneratorCeiling n := by
  rcases h with ⟨hn,hH⟩ | ⟨hn,hH⟩ | ⟨hn,hH⟩ | ⟨hn,hH⟩
  · exact hH.trans (lower_at n 32 15 5 (by decide) hn (by decide) (by decide) (by decide))
  · exact hH.trans (lower_at n 64 26 6 (by decide) hn (by decide) (by decide) (by decide))
  · exact hH.trans (lower_at n 128 33 7 (by decide) hn (by decide) (by decide) (by decide))
  · exact hH.trans (lower_at n 256 51 8 (by decide) hn (by decide) (by decide) (by decide))

theorem small_profile_ceiling (n H : ℕ)
    (h : (9 ≤ n ∧ H ≤ 5) ∨ (16 ≤ n ∧ H ≤ 8) ∨ (24 ≤ n ∧ H ≤ 11)) :
    H ≤ traceyPermutationGeneratorCeiling n := by
  rcases h with ⟨hn,hH⟩ | ⟨hn,hH⟩ | ⟨hn,hH⟩
  · exact hH.trans (lower_at n 9 5 4 (by decide) hn (by decide) (by decide) (by decide))
  · exact hH.trans (lower_at n 16 8 4 (by decide) hn (by decide) (by decide) (by decide))
  · exact hH.trans (lower_at n 24 11 5 (by decide) hn (by decide) (by decide) (by decide))

end SymmetricSubgroupAsymptotics.UnitaryBoundedPrimitiveOrdinaryNumerics
