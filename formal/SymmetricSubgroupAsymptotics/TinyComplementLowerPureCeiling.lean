import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate
import SymmetricSubgroupAsymptotics.TraceyAffineInducedModuleInput

/-! Universal small-primary pure-top ceiling comparisons. The entire
five-to-nine interval is handled by two rational root bounds and ceiling
translation; no separate top-degree table is needed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TinyComplementLowerPureCeiling

theorem one_add_ceiling_le_double (t : ℕ) (ht5 : 5 ≤ t) (ht9 : t ≤ 9) :
    1+traceyPermutationGeneratorCeiling t ≤ traceyPermutationGeneratorCeiling (2*t) := by
  let L := Real.logb 2 (t : ℝ)
  let U := Real.logb 2 ((2*t : ℕ) : ℝ)
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have ht5R : (5 : ℝ) ≤ t := by exact_mod_cast ht5
  have hL : (9/4 : ℝ) ≤ L := by
    have hp := Nat.pow_le_pow_left ht5 4
    have hh := IntegerLogSquareRootCeilingCertificate.log_lower t 4 9
      (by omega) (by decide) ((by decide : 2^9 ≤ 5^4).trans hp)
    simpa only [L,Nat.cast_ofNat] using hh
  have hU : U ≤ (17/4 : ℝ) := by
    have ht18 : 2*t ≤ 18 := by omega
    have hp := Nat.pow_le_pow_left ht18 4
    have hh := IntegerLogSquareRootCeilingCertificate.log_upper (2*t) 4 17
      (by omega) (by decide) (hp.trans (by decide : 18^4 ≤ 2^17))
    simpa only [U,Nat.cast_ofNat] using hh
  have hL0 : 0 < L := by linarith only [hL]
  have hU0 : 0 < U := Real.logb_pos (by norm_num)
    (by exact_mod_cast (show 1 < 2*t by omega))
  have hrootL : (3/2 : ℝ) ≤ Real.sqrt L := by
    have hs := Real.sq_sqrt hL0.le
    nlinarith only [hs,Real.sqrt_nonneg L,hL]
  have hrootU : Real.sqrt U ≤ (21/10 : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    linarith only [hU]
  have hsource := div_le_div_of_nonneg_left htR.le
    (by norm_num : (0 : ℝ) < 3/2) hrootL
  have htarget := div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 2*(t : ℝ))
    (Real.sqrt_pos.mpr hU0) hrootU
  have hgap : (t : ℝ)/Real.sqrt L+1 ≤ 2*(t : ℝ)/Real.sqrt U := by
    nlinarith only [hsource,htarget,ht5R]
  have hh := Nat.ceil_mono hgap
  rw [Nat.ceil_add_one (div_nonneg htR.le (Real.sqrt_nonneg L))] at hh
  simpa only [traceyPermutationGeneratorCeiling,L,U,Nat.cast_mul,Nat.cast_ofNat,
    Nat.add_comm] using hh

theorem four_add_ceiling_five_le : 4+traceyPermutationGeneratorCeiling 5 ≤
    traceyPermutationGeneratorCeiling 20 := by
  have htop : traceyPermutationGeneratorCeiling 5 ≤ 4 :=
    IntegerLogSquareRootCeilingCertificate.ceil_le_of_square 5 1 2 4
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have htarget : 8 ≤ traceyPermutationGeneratorCeiling 20 :=
    IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 20 1 5 8
      (by decide) (by decide) (by decide) (by decide) (by decide)
  omega

end SymmetricSubgroupAsymptotics.TinyComplementLowerPureCeiling
