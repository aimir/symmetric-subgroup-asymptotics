import SymmetricSubgroupAsymptotics.WeightedCounting

/-!
# Numerical hot/cold fusion

Only the retained source weight is raised to a moment power. The cocycle
factor remains outside the moment. These inequalities expose all their
input envelopes and do not assume a bound on the normalized subgroup count.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Filter

namespace SymmetricSubgroupAsymptotics

/-- The elementary moment inequality on one hot source. -/
theorem fusion_hot_weight_le {x t : ℝ} (ht : 0 < t) (hx : t ≤ x)
    {q : ℕ} (hq : 1 ≤ q) : x ≤ x^q / t^(q-1) := by
  apply (le_div_iff₀ (pow_pos ht _)).mpr
  have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.le hx (q-1))
    (ht.le.trans hx)
  have he : x * x^(q-1) = x^q := by rw [← pow_succ']; congr 1; omega
  exact h.trans_eq he

/-- The complete hot union is bounded against a single same-source moment.
The factor D is charged once, outside the power q. -/
theorem fusion_hot_sum_le {ι : Type*} [Fintype ι]
    (f Φ : ι → ℝ) {D t M : ℝ} (hD : 0 ≤ D) (ht : 0 < t)
    (hΦ : ∀ i, 0 ≤ Φ i) (hf : ∀ i, f i ≤ D * Φ i)
    {q : ℕ} (hq : 1 ≤ q) (hmoment : ∑ i, Φ i ^ q ≤ M) :
    (∑ i ∈ Finset.univ.filter (fun i ↦ t < Φ i), f i) ≤ D / t^(q-1) * M := by
  calc
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i ↦ t < Φ i), D / t^(q-1) * Φ i^q := by
      apply Finset.sum_le_sum
      intro i hi
      have hhot := (Finset.mem_filter.mp hi).2
      have h := mul_le_mul_of_nonneg_left (fusion_hot_weight_le ht hhot.le hq) hD
      exact (hf i).trans (by convert h using 1; ring)
    _ ≤ ∑ i, D / t^(q-1) * Φ i^q := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro i _ _
      exact mul_nonneg (div_nonneg hD (pow_pos ht _).le) (pow_nonneg (hΦ i) _)
    _ = D / t^(q-1) * ∑ i, Φ i^q := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hmoment (div_nonneg hD (pow_pos ht _).le)

/-- The exact exponent identity governing the hot moment choice. -/
theorem fusion_hot_square (b w v e q : ℝ) (hv : v ≠ 0) :
    (b+q*v)^2/16 - (q-1)*(v/8+e)*b + ((w-v-16*e)/8)*b - (b+w)^2/16 =
      -4*e^2*b^2/v^2 - e*b - w^2/16 + v^2/16*(q-8*e*b/v^2)^2 := by
  field_simp
  ring

/-- A positive integer moment, including the small-b endpoint. -/
def fusionMoment (e v b : ℝ) : ℕ := max 1 ⌈8*e*b/v^2⌉₊

theorem fusionMoment_pos (e v b : ℝ) : 1 ≤ fusionMoment e v b := le_max_left _ _

theorem fusionMoment_distance {e v b : ℝ} (he : 0 ≤ e) (hb : 0 ≤ b) :
    0 ≤ (fusionMoment e v b : ℝ)-8*e*b/v^2 ∧
      (fusionMoment e v b : ℝ)-8*e*b/v^2 ≤ 1 := by
  have hx : 0 ≤ 8*e*b/v^2 := by positivity
  have hlo := Nat.le_ceil (8*e*b/v^2)
  have hhi := Nat.ceil_lt_add_one hx
  by_cases h : ⌈8*e*b/v^2⌉₊ ≤ 1
  · have hceil : (⌈8*e*b/v^2⌉₊ : ℝ) ≤ 1 := by exact_mod_cast h
    simp only [fusionMoment,max_eq_left h,Nat.cast_one]
    constructor <;> linarith
  · have h : 1 ≤ ⌈8*e*b/v^2⌉₊ := by omega
    simp only [fusionMoment,max_eq_right h]
    constructor <;> linarith

/-- Rounding costs at most v²/16, uniformly even at b=0. -/
theorem fusion_hot_exponent_le {e v b w : ℝ}
    (he : 0 ≤ e) (hb : 0 ≤ b) (hv : v ≠ 0) :
    (b+(fusionMoment e v b : ℝ)*v)^2/16 -
      ((fusionMoment e v b : ℝ)-1)*(v/8+e)*b + ((w-v-16*e)/8)*b -
      (b+w)^2/16 ≤ -4*e^2*b^2/v^2-e*b-w^2/16+v^2/16 := by
  rw [fusion_hot_square b w v e _ hv]
  obtain ⟨hlo,hhi⟩ := fusionMoment_distance (v := v) he hb
  have hs : ((fusionMoment e v b : ℝ)-8*e*b/v^2)^2 ≤ 1 := by nlinarith
  have h := mul_le_mul_of_nonneg_left hs (show 0 ≤ v^2/16 by positivity)
  linarith

end SymmetricSubgroupAsymptotics
