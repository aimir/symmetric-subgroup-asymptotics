import SymmetricSubgroupAsymptotics.Non2PreE7Sns2RankTailPhysical

/-!
# Uniform numerical gaps for SNS2

These are the three homogeneous inequalities behind the all-width SNS2
aggregation.  They retain the quotient rank `ℓ` until the single constraint
`3ℓ ≤ w` is applied.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- The cold SNS2 main exponent has simultaneous `wb` and `w²` reserve. -/
theorem sns2_cold_main_gap {b w l : ℕ} (hl : 3 * l ≤ w) :
    (-(((b + w : ℕ) : ℝ) ^ 2) / 16 + (b : ℝ) ^ 2 / 16 +
        (l : ℝ) * (51 / 200) * b + (l : ℝ) ^ 2 / 4) ≤
      -(w : ℝ) * b / 25 - 5 * (w : ℝ) ^ 2 / 144 := by
  have hlR : 3 * (l : ℝ) ≤ w := by exact_mod_cast hl
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hw0 : (0 : ℝ) ≤ w := by positivity
  have hl0 : (0 : ℝ) ≤ l := by positivity
  have hcross : (l : ℝ) * (51 / 200) * b ≤
      (w : ℝ) * (17 / 200) * b := by
    nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hlR)]
  have hsquare : (l : ℝ) ^ 2 / 4 ≤ (w : ℝ) ^ 2 / 36 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlR)
      (show 0 ≤ 3 * (l : ℝ) + w by positivity)]
  push_cast
  nlinarith

/-- The same cold main exponent already dominates a fixed multiple of the
full removed-width product `w(b+w)`. -/
theorem sns2_cold_main_gap_product {b w l : ℕ} (hl : 3 * l ≤ w) :
    (-(((b + w : ℕ) : ℝ) ^ 2) / 16 + (b : ℝ) ^ 2 / 16 +
        (l : ℝ) * (51 / 200) * b + (l : ℝ) ^ 2 / 4) ≤
      -(5 / 144 : ℝ) * w * (b + w) := by
  have h := sns2_cold_main_gap (b := b) hl
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hw0 : (0 : ℝ) ≤ w := by positivity
  push_cast at h ⊢
  nlinarith

/-- Version of the cold gap in the exact parity-uniform exponent produced by
`fusionWidthColdKernel_quadratic_le`.  The constant `2` covers the finitely
many smallest odd widths; the two negative terms are uniform. -/
theorem sns2_halfDegree_cold_main_gap {b w l : ℕ}
    (hw : 5 ≤ w) (hl : 3 * l ≤ w) :
    (-(halfDegree w : ℝ) * b / 4 - (halfDegree w : ℝ) ^ 2 / 4 +
        (halfDegree w : ℝ) / 4 + 1 / 4 +
        (l : ℝ) * (51 / 200) * b + (l : ℝ) ^ 2 / 4) ≤
      -(w : ℝ) * b / 80 - (w : ℝ) ^ 2 / 80 + 2 := by
  let r := halfDegree w
  have hrw : 2 * r ≤ w := by
    dsimp [r, halfDegree]
    omega
  have hwr : w ≤ 2 * r + 1 := by
    dsimp [r, halfDegree]
    omega
  have hlR : 3 * (l : ℝ) ≤ w := by exact_mod_cast hl
  have hrwR : 2 * (r : ℝ) ≤ w := by exact_mod_cast hrw
  have hwrR : (w : ℝ) ≤ 2 * r + 1 := by exact_mod_cast hwr
  have hwR : (5 : ℝ) ≤ w := by exact_mod_cast hw
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hw0 : (0 : ℝ) ≤ w := by positivity
  have hl0 : (0 : ℝ) ≤ l := by positivity
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hcross :
      -(r : ℝ) * b / 4 + (l : ℝ) * (51 / 200) * b ≤
        -(w : ℝ) * b / 80 := by
    have h₁ := mul_nonneg hb0 (sub_nonneg.mpr hlR)
    have h₂ := mul_nonneg hb0 (sub_nonneg.mpr hwrR)
    nlinarith
  have hsquareL : (3 * (l : ℝ)) ^ 2 ≤ (w : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlR)
      (show 0 ≤ 3 * (l : ℝ) + w by positivity)]
  have hsquareR : ((w : ℝ) - 1) ^ 2 ≤ (2 * (r : ℝ)) ^ 2 := by
    have hleft : 0 ≤ (w : ℝ) - 1 := by linarith
    have hle : (w : ℝ) - 1 ≤ 2 * r := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hle)
      (show 0 ≤ (w : ℝ) - 1 + 2 * r by positivity)]
  have hsquare :
      -(r : ℝ) ^ 2 / 4 + (r : ℝ) / 4 + 1 / 4 +
          (l : ℝ) ^ 2 / 4 ≤
        -(w : ℝ) ^ 2 / 80 + 2 := by
    nlinarith
  dsimp [r] at hcross hsquare ⊢
  linarith

/-- In the first hot regime, square completion leaves the full
`1/40000` quadratic reserve after the target normal-count cost. -/
theorem sns2_firstRegime_main_gap {b w l : ℕ} (hl : 3 * l ≤ w) :
    (-(((b + w : ℕ) : ℝ) ^ 2) / 16 + (b : ℝ) ^ 2 / 16 -
        (b : ℝ) ^ 2 / 40000 +
        (l : ℝ) * (51 / 200) * b + (l : ℝ) ^ 2 / 4) ≤
      -(((b + w : ℕ) : ℝ) ^ 2) / 40000 := by
  have h := sns2_cold_main_gap (b := b) hl
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hw0 : (0 : ℝ) ≤ w := by positivity
  push_cast at h ⊢
  nlinarith

/-- Before using the second-regime width fraction, its main exponent has the
uniform mixed reserve `-wb/24-w²/144`. -/
theorem sns2_secondRegime_main_gap {b w l : ℕ} (hl : 3 * l ≤ w) :
    (-(((b + w : ℕ) : ℝ) ^ 2) / 16 +
        ((b : ℝ) + 2 * l) ^ 2 / 16 + (l : ℝ) ^ 2 / 4) ≤
      -(w : ℝ) * b / 24 - (w : ℝ) ^ 2 / 144 := by
  have hlR : 3 * (l : ℝ) ≤ w := by exact_mod_cast hl
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hw0 : (0 : ℝ) ≤ w := by positivity
  have hl0 : (0 : ℝ) ≤ l := by positivity
  have hcross : (b : ℝ) * l / 4 ≤ (b : ℝ) * w / 12 := by
    nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hlR)]
  have hsquare : (l : ℝ) ^ 2 / 2 ≤ (w : ℝ) ^ 2 / 18 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlR)
      (show 0 ≤ 3 * (l : ℝ) + w by positivity)]
  push_cast
  nlinarith

/-- The second-regime inequality `b < 100ℓ`, together with `3ℓ ≤ w`, forces
the removed width to occupy more than `3/103` of the ambient degree. -/
theorem sns2_secondRegime_width_fraction {b w l : ℕ}
    (hl : 3 * l ≤ w) (hregime : (b : ℝ) < 100 * l) :
    (3 : ℝ) * (b + w) < 103 * w := by
  have hlR : 3 * (l : ℝ) ≤ w := by exact_mod_cast hl
  linarith

/-- Consequently the second hot regime has a stronger quadratic reserve
than the `1/40000` reserve used uniformly for SNS2. -/
theorem sns2_secondRegime_quadratic_gap {b w l : ℕ}
    (hl : 3 * l ≤ w) (hregime : (b : ℝ) < 100 * l) :
    (-(((b + w : ℕ) : ℝ) ^ 2) / 16 +
        ((b : ℝ) + 2 * l) ^ 2 / 16 + (l : ℝ) ^ 2 / 4) <
      -(((b + w : ℕ) : ℝ) ^ 2) / 4944 := by
  have hmain := sns2_secondRegime_main_gap (b := b) hl
  have hfrac := sns2_secondRegime_width_fraction hl hregime
  have hn0 : (0 : ℝ) ≤ b + w := by positivity
  have hw0 : (0 : ℝ) ≤ w := by positivity
  have hprod : ((b + w : ℕ) : ℝ) ^ 2 <
      (103 / 3 : ℝ) * w * (b + w) := by
    push_cast at hfrac ⊢
    nlinarith [mul_pos (show (0 : ℝ) < 3 by norm_num)
      (show 0 < 103 by norm_num)]
  push_cast at hmain ⊢
  nlinarith

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
