import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Uniform quadratic loss in the complete marker row

The exact constraints on the defect and the number of repeated signs
give the same loss at both parities. Two polynomial factorizations replace
division by the degree and convexity arguments at moving endpoints.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.MarkerQuadraticDeficit

def quadratic (N D k lambda : ℝ) : ℝ :=
  -N * (D + k) / 2 + (D + k) ^ 2 / 4 + lambda * k ^ 2 / 4

/-- The coefficient 13/60 is uniform over the full feasible region,
including the endpoint where the collapsed degree is zero. -/
theorem quadratic_le {N D k lambda : ℝ}
    (hD : 0 ≤ D) (hDN : D ≤ N) (hk : 0 ≤ k)
    (hkD : k ≤ 2 * D) (hkN : k ≤ N - D) (hlambda : lambda ≤ 8 / 5) :
    quadratic N D k lambda ≤ -13 * N * D / 60 := by
  have hpoly : 15 * D ^ 2 + 30 * D * k + 39 * k ^ 2 ≤
      17 * N * D + 30 * N * k := by
    by_cases hsmall : 3 * D ≤ N
    · have hfirst := mul_nonneg
        (show 0 ≤ 17 * D + 30 * k by linarith) (sub_nonneg.mpr hsmall)
      have hsecond := mul_nonneg (sub_nonneg.mpr hkD)
        (show 0 ≤ 39 * k + 18 * D by linarith)
      nlinarith
    · have hfirst := mul_nonneg
        (show 0 ≤ 3 * D - N by linarith) (show 0 ≤ 9 * N - 8 * D by linarith)
      have hsecond := mul_nonneg (sub_nonneg.mpr hkN)
        (show 0 ≤ 39 * k + 9 * (N - D) by linarith)
      nlinarith
  have hloss := mul_nonneg (sub_nonneg.mpr hlambda) (sq_nonneg k)
  unfold quadratic
  nlinarith

end SymmetricSubgroupAsymptotics.MarkerQuadraticDeficit

end
