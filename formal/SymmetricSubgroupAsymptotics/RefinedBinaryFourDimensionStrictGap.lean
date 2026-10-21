import SymmetricSubgroupAsymptotics.TraceyRefinedAffineInput
import Mathlib.Data.Nat.Factorization.Basic

/-! A strict generic induced-capacity gap for four-dimensional binary
local modules. Only block counts2 and4 are excluded; those are precisely
the two fixed actual cold-rank cells. No affine subgroup census occurs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

/-- A deliberately coarse strict gap, sufficient for the actual8s-point
comparator. The exact central-binomial improvement is not needed here. -/
theorem refined_binary_four_capacity_strict_gap
    {s : ℕ} {H : ℝ} (hs : 2 ≤ s) (hs2 : s ≠ 2) (hs4 : s ≠ 4)
    (hb : TraceyRefinedInducedCapacityBounds 2 4 s H) :
    H ≤ (19/10 : ℝ)*s := by
  have hs0 : s ≠ 0 := by omega
  have hsR : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  by_cases ho : ordCompl[2] s=1
  · let e := s.factorization 2
    have hseq : s=2^e := by
      simpa only [e,ho,mul_one] using (Nat.ordProj_mul_ordCompl_eq_self s 2).symm
    have he : 3 ≤ e := by
      by_contra hn
      have he2 : e ≤ 2 := by omega
      interval_cases e <;> norm_num at hseq <;> omega
    have heR : (3 : ℝ) ≤ e := by exact_mod_cast he
    have hpos : (0 : ℝ)<3*(e : ℝ) := by positivity
    have hmax : ¬2^(e+1) ∣ s := by
      rw [hseq]
      exact Nat.not_dvd_of_pos_of_lt (pow_pos (by decide) e)
        (Nat.pow_lt_pow_right (by decide : 1<2) (by omega))
    have hh := hb.primary e (by omega) (by rw [hseq]) hmax
    have hroot : Real.sqrt (2/(3*(e : ℝ))) ≤ (19/40 : ℝ) := by
      apply (Real.sqrt_le_iff).mpr
      constructor
      · norm_num
      · apply (div_le_iff₀ hpos).mpr
        nlinarith
    have hh' : H ≤ 4*(s : ℝ)*Real.sqrt (2/(3*(e : ℝ))) := by
      simpa only [Nat.cast_ofNat,show (2 : ℝ)-1=1 by norm_num,mul_one] using hh
    exact hh'.trans ((mul_le_mul_of_nonneg_left hroot (by positivity)).trans_eq (by ring))
  · obtain ⟨q,hq,hdiv⟩ := Nat.exists_prime_and_dvd ho
    have hq2 : q ≠ 2 := by
      intro heq
      subst q
      exact Nat.not_dvd_ordCompl Nat.prime_two hs0 hdiv
    have hq3 : 3 ≤ q := by have := hq.two_le; omega
    have hqR : (0 : ℝ)<q := by exact_mod_cast hq.pos
    have hq3R : (3 : ℝ) ≤ q := by exact_mod_cast hq3
    have hh := hb.primeTo q 1 hq hq2 (by decide)
      (by simpa only [pow_one] using hdiv.trans (Nat.ordCompl_dvd s 2))
    simp only [pow_one,Nat.cast_ofNat] at hh
    apply hh.trans
    apply (div_le_iff₀ hqR).mpr
    have hmul := mul_le_mul_of_nonneg_right hq3R hsR
    nlinarith

end SymmetricSubgroupAsymptotics
