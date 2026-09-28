import SymmetricSubgroupAsymptotics.GrowingQuotientHotKernel

/-!
# Uniform degree bounds for the growing quotient graph

The rounded moment creates a subgroup at degree `b + q*v`.  For a nontrivial
comparator the padded representation degree is between `ρ*w` and `w`, while
the residual margin satisfies `δ ≤ w/8`.  These facts bound the graph degree
above by the manuscript's explicit linear expression and below by `ρ*(b+w)`.
The lower bound makes the coarse subgroup estimate uniform in the ambient
degree; the upper bound controls its quadratic error.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- The rounded graph degree has the manuscript's uniform linear upper
bound. -/
theorem growingQuotientGraphDegree_upper
    {ρ δ : ℝ} (b w v : ℕ)
    (hρ : 0 < ρ) (hδ : 0 ≤ δ) (hv : 0 < v)
    (hδupper : δ ≤ (w : ℝ) / 8)
    (hvlower : ρ * w ≤ (v : ℝ))
    (hvupper : (v : ℝ) ≤ w) :
    (growingQuotientGraphDegree δ b v : ℝ) ≤
      (1 + 1 / (2 * ρ)) * b + w := by
  let q := growingQuotientMoment δ (v : ℝ) (b : ℝ)
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  have hq := (growingQuotientMoment_distance hδ (by positivity : (0 : ℝ) ≤ b)
    (v := (v : ℝ))).2
  have hδv : 4 * δ / (v : ℝ) ≤ (w : ℝ) / (2 * v) := by
    rw [show (w : ℝ) / (2 * v) = ((w : ℝ) / 2) / v by field_simp]
    apply (div_le_div_iff_of_pos_right hvR).2
    nlinarith
  have hwv : (w : ℝ) / (v : ℝ) ≤ 1 / ρ := by
    apply (div_le_iff₀ hvR).2
    calc
      (w : ℝ) ≤ (v : ℝ) / ρ := (le_div_iff₀ hρ).2 (by nlinarith)
      _ = 1 / ρ * v := by field_simp
  have hδρ : 4 * δ / (v : ℝ) ≤ 1 / (2 * ρ) := by
    calc
      _ ≤ (w : ℝ) / (2 * v) := hδv
      _ = ((w : ℝ) / v) / 2 := by ring
      _ ≤ (1 / ρ) / 2 := div_le_div_of_nonneg_right hwv (by norm_num)
      _ = _ := by ring
  have hqv : (q : ℝ) * (v : ℝ) ≤
      (1 / (2 * ρ)) * b + w := by
    have hq' : (q : ℝ) ≤ 4 * δ * b / (v : ℝ) ^ 2 + 1 := by linarith
    have hm := mul_le_mul_of_nonneg_right hq' hvR.le
    have hb0 : 0 ≤ (b : ℝ) := by positivity
    have hslope := mul_le_mul_of_nonneg_right hδρ hb0
    calc
      (q : ℝ) * v ≤ (4 * δ * b / (v : ℝ) ^ 2 + 1) * v := hm
      _ = (4 * δ / (v : ℝ)) * b + v := by field_simp
      _ ≤ (1 / (2 * ρ)) * b + w := add_le_add hslope hvupper
  change ((b + q * v : ℕ) : ℝ) ≤ _
  push_cast
  linarith

/-- A nontrivial padded comparator forces the graph degree to grow linearly
with the ambient degree. -/
theorem growingQuotientGraphDegree_lower
    {ρ δ : ℝ} (b w v : ℕ)
    (hρ1 : ρ ≤ 1)
    (hvlower : ρ * w ≤ (v : ℝ)) :
    ρ * (b + w) ≤ (growingQuotientGraphDegree δ b v : ℝ) := by
  have hq : 1 ≤ growingQuotientMoment δ (v : ℝ) (b : ℝ) :=
    growingQuotientMoment_pos δ (v : ℝ) (b : ℝ)
  have hqv : (v : ℝ) ≤
      (growingQuotientMoment δ (v : ℝ) (b : ℝ) : ℝ) * v := by
    have hv0 : 0 ≤ (v : ℝ) := by positivity
    nlinarith [show (1 : ℝ) ≤ growingQuotientMoment δ (v : ℝ) (b : ℝ) by
      exact_mod_cast hq]
  unfold growingQuotientGraphDegree
  push_cast
  have hb : ρ * b ≤ (b : ℝ) := by
    have hb0 : 0 ≤ (b : ℝ) := by positivity
    nlinarith
  linarith

/-- A linear graph-degree upper bound converts the coarse quadratic error
into a prescribed fraction of the ambient quadratic reserve. -/
theorem growingQuotient_coarse_error_le
    {ρ ε L M n : ℝ}
    (hε : 0 ≤ ε) (hM : 0 ≤ M) (hL : 0 ≤ L) (hn : 0 ≤ n)
    (hdegree : M ≤ L * n)
    (hεL : ε * L ^ 2 ≤ ρ ^ 2 / 16) :
    ε * M ^ 2 ≤ ρ ^ 2 * n ^ 2 / 16 := by
  have hsq : M ^ 2 ≤ (L * n) ^ 2 := (sq_le_sq₀ hM (mul_nonneg hL hn)).2 hdegree
  calc
    ε * M ^ 2 ≤ ε * (L * n) ^ 2 := mul_le_mul_of_nonneg_left hsq hε
    _ = (ε * L ^ 2) * n ^ 2 := by ring
    _ ≤ (ρ ^ 2 / 16) * n ^ 2 :=
      mul_le_mul_of_nonneg_right hεL (sq_nonneg n)
    _ = _ := by ring

end SymmetricSubgroupAsymptotics

end
