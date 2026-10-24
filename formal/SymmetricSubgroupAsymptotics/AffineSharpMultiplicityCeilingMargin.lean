import SymmetricSubgroupAsymptotics.LargeOrbitGeneratorNumerics
import Mathlib.Data.Real.Sqrt

/-! A shared sufficient margin for the genuine half and sharper-log
ordinary costs, including the ACTUAL rounded top ceiling. The lemma is
pure scalar arithmetic; later original-action consumers must derive its
margin from their actual local degree and actual complement order. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AffineSharpMultiplicityCeilingMargin

theorem aggregate_le (C s R g : ℝ) (t : ℕ)
    (hC : 0 ≤ C) (hs : 0 ≤ s) (hR : 0 ≤ R) (hg : 0 ≤ g) (ht : 2 ≤ t)
    (hmargin : (C+2)^2*(9*s+64) ≤ 36*R^2)
    (hhalf : g ≤ C*(t : ℝ)/2+
      (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ))
    (hlog : g ≤ Real.sqrt (5/3)*C*(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))+
      (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ)) :
    g ≤ R*(t : ℝ)/Real.sqrt (s+Real.logb 2 (t : ℝ)) := by
  let L := Real.logb 2 (t : ℝ)
  let B := C+2
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have hB : 0 ≤ B := by dsimp only [B]; linarith only [hC]
  have hL1 : 1 ≤ L := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2) htR
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using hh
  have hL : 0 < L := by linarith only [hL1]
  have hrootL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hrootS : 0 < Real.sqrt (s+L) := Real.sqrt_pos.mpr (by linarith only [hs,hL])
  have hs1 : 1 ≤ Real.sqrt L := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hL1
  have hsle : Real.sqrt L ≤ (t : ℝ) :=
    (Real.sqrt_le_iff).mpr ⟨ht0,LargeOrbitGeneratorNumerics.logb_le_square htR⟩
  have hunit : (1 : ℝ) ≤ (t : ℝ)/Real.sqrt L :=
    (le_div_iff₀ hrootL).mpr (by simpa only [one_mul] using hsle)
  have hdiv : (t : ℝ)/Real.sqrt L ≤ (t : ℝ) :=
    (div_le_iff₀ hrootL).mpr
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hs1 ht0)
  have hceilNat : ⌈(t : ℝ)/Real.sqrt L⌉₊ ≤ t := Nat.ceil_le.mpr hdiv
  have hceilR : (⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) ≤ t := by exact_mod_cast hceilNat
  have hceil : (⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) ≤ (t : ℝ)/Real.sqrt L+1 :=
    (Nat.ceil_lt_add_one (div_nonneg ht0 hrootL.le)).le
  change g ≤ C*(t : ℝ)/2+(⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) at hhalf
  change g ≤ Real.sqrt (5/3)*C*(t : ℝ)/Real.sqrt L+
    (⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) at hlog
  have hhalf' : g ≤ B*(t : ℝ)/2 := by
    dsimp only [B]
    linarith only [hhalf,hceilR]
  have halpha : Real.sqrt (5/3 : ℝ) ≤ 4/3 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5/3),
      Real.sqrt_nonneg (5/3 : ℝ)]
  have halphaC := mul_le_mul_of_nonneg_right halpha
    (show 0 ≤ C*(t : ℝ)/Real.sqrt L by positivity)
  have hlog' : g ≤ (4/3)*B*(t : ℝ)/Real.sqrt L := by
    have hunit2 : (t : ℝ)/Real.sqrt L+1 ≤ 2*((t : ℝ)/Real.sqrt L) := by
      linarith only [hunit]
    have ha : Real.sqrt (5/3)*C*(t : ℝ)/Real.sqrt L ≤ (4/3)*C*(t : ℝ)/Real.sqrt L := by
      convert halphaC using 1 <;> ring
    calc
      g ≤ Real.sqrt (5/3)*C*(t : ℝ)/Real.sqrt L+
          (⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) := hlog
      _ ≤ (4/3)*C*(t : ℝ)/Real.sqrt L+2*((t : ℝ)/Real.sqrt L) :=
        add_le_add ha (hceil.trans hunit2)
      _ ≤ (4/3)*B*(t : ℝ)/Real.sqrt L := by
        dsimp only [B]
        have hh : 0 ≤ (t : ℝ)/Real.sqrt L := by positivity
        calc
          (4/3)*C*(t : ℝ)/Real.sqrt L+2*((t : ℝ)/Real.sqrt L) =
              ((4/3)*C+2)*((t : ℝ)/Real.sqrt L) := by ring
          _ ≤ ((4/3)*(C+2))*((t : ℝ)/Real.sqrt L) :=
            mul_le_mul_of_nonneg_right (by linarith) hh
          _ = (4/3)*(C+2)*(t : ℝ)/Real.sqrt L := by ring
  have hhalfSq : g^2 ≤ (1/4)*B^2*(t : ℝ)^2 := by
    have hh := (sq_le_sq₀ hg (show 0 ≤ B*(t : ℝ)/2 by positivity)).mpr hhalf'
    convert hh using 1 <;> ring
  have hlogSq : g^2*L ≤ (16/9)*B^2*(t : ℝ)^2 := by
    have hm := (le_div_iff₀ hrootL).mp hlog'
    have hh := (sq_le_sq₀ (mul_nonneg hg hrootL.le)
      (show 0 ≤ (4/3)*B*(t : ℝ) by positivity)).mpr hm
    rw [mul_pow,Real.sq_sqrt hL.le] at hh
    convert hh using 1 <;> ring
  have hmarg : B^2*(9*s+64)/36 ≤ R^2 := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 36)).mpr
    simpa only [B,mul_comm] using hmargin
  have hsq : (g*Real.sqrt (s+L))^2 ≤ (R*(t : ℝ))^2 := by
    calc
      _ = g^2*(s+L) := by rw [mul_pow,Real.sq_sqrt (by linarith only [hs,hL])]
      _ = g^2*s+g^2*L := by ring
      _ ≤ ((1/4)*B^2*(t : ℝ)^2)*s+(16/9)*B^2*(t : ℝ)^2 :=
        add_le_add (mul_le_mul_of_nonneg_right hhalfSq hs) hlogSq
      _ = (B^2*(9*s+64)/36)*(t : ℝ)^2 := by ring
      _ ≤ R^2*(t : ℝ)^2 := mul_le_mul_of_nonneg_right hmarg (sq_nonneg _)
      _ = (R*(t : ℝ))^2 := (mul_pow _ _ _).symm
  have hh := (sq_le_sq₀ (mul_nonneg hg hrootS.le) (mul_nonneg hR ht0)).mp hsq
  exact (le_div_iff₀ hrootS).mpr hh

end SymmetricSubgroupAsymptotics.AffineSharpMultiplicityCeilingMargin
