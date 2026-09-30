import SymmetricSubgroupAsymptotics.GrowingMenuMassEntryCertificate
import SymmetricSubgroupAsymptotics.BinaryMixtureAbsorption

/-!
# Growing menu mass from a linear/log-squared entry envelope

The pre-`E7` templates naturally produce coefficients bounded by

`K * 2^(L*w + C*w*log(n+2)^2)`.

This file proves once that such an entry envelope, together with a
subquadratic width-index count, is a `GrowingMenuMassBound`.  The constants
`K`, `L`, and `C` are uniform; no fixed-width cutoff is used.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {ι : ℕ → Type*} [∀ w, Fintype (ι w)]

/-- A uniform pre-division numerator envelope with linear width cost and a
width times log-squared ambient cost. -/
def LinearLogSquaredMenuNumeratorBound (w₀ : ℕ)
    (D : ∀ w, ι w → ℕ → ℝ) : Prop :=
  ∃ K L C : ℝ, 0 ≤ K ∧ 0 ≤ L ∧ 0 ≤ C ∧
    ∀ n w, w ∈ Finset.Ico w₀ (n + 1) → ∀ i,
      D w i (n - w) ≤
        K * (2 : ℝ) ^
          (L * w + C * w * Real.log ((n : ℝ) + 2) ^ 2)

private theorem eventually_const_le_two_rpow
    {K gamma : ℝ} (hK : 0 ≤ K) (hgamma : 0 < gamma) :
    ∀ᶠ n : ℕ in atTop, K ≤ (2 : ℝ) ^ (gamma * n) := by
  filter_upwards [eventually_exponential_le_inv_rpow hgamma 1,
    eventually_ge_atTop (max 1 ⌈K⌉₊)] with n hexp hn
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have hexp' : (2 : ℝ) ^ (-gamma * n) ≤ 1 / (n : ℝ) := by
    simpa using hexp
  have hKn : K ≤ (n : ℝ) :=
    (Nat.le_ceil K).trans
      (by exact_mod_cast (le_max_right 1 ⌈K⌉₊).trans hn)
  have hsmall : K * (2 : ℝ) ^ (-gamma * n) ≤ 1 := by
    calc
      K * (2 : ℝ) ^ (-gamma * n) ≤ K * (1 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hexp' hK
      _ ≤ 1 := by
        rw [mul_one_div]
        exact (div_le_one hnpos).2 hKn
  calc
    K = (K * (2 : ℝ) ^ (-gamma * n)) *
        (2 : ℝ) ^ (gamma * n) := by
      rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      rw [show -gamma * (n : ℝ) + gamma * n = 0 by ring,
        Real.rpow_zero, mul_one]
    _ ≤ 1 * (2 : ℝ) ^ (gamma * n) :=
      mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ = _ := one_mul _

/-- A linear/log-squared numerator envelope and a subquadratic action count
give the direct growing menu mass, with the original divisor retained. -/
theorem growingMenuMassBound_of_linearLogSquared
    {w₀ : ℕ} (hw₀ : 1 ≤ w₀)
    (D : ∀ w, ι w → ℕ → ℝ) (A : ∀ w, ι w → ℝ)
    (hD : ∀ w i b, 0 ≤ D w i b)
    (hA : ∀ w i, 1 ≤ A w i)
    (hindex : SubquadraticMenuIndexCount ι)
    (henvelope : LinearLogSquaredMenuNumeratorBound w₀ D) :
    GrowingMenuMassBound w₀ D A := by
  obtain ⟨K, L, C, hK, hL, hC, hentry⟩ := henvelope
  intro gamma hgamma
  have hquarter : 0 < gamma / 4 := by positivity
  obtain ⟨B, hB, hcount⟩ := hindex (gamma / 4) hquarter
  let delta : ℝ := Real.sqrt (gamma / 4)
  have hdelta : 0 < delta := Real.sqrt_pos.2 hquarter
  filter_upwards [
      BinaryMixtureNumerics.eventually_log_error_le_sqrt
        (Real.sqrt C) (Real.sqrt_nonneg C) hdelta,
      eventually_const_le_two_rpow (K := B * K) (gamma := gamma / 4)
        (mul_nonneg hB hK) hquarter,
      eventually_ge_atTop (max 1 ⌈4 * L / gamma⌉₊)] with n hlog hconst hn
  intro w hw
  have hww := Finset.mem_Ico.mp hw
  have hwn : w ≤ n := by omega
  have hw1 : (1 : ℝ) ≤ w := by
    exact_mod_cast hw₀.trans hww.1
  have hw0 : (0 : ℝ) ≤ w := zero_le_one.trans hw1
  have hwnR : (w : ℝ) ≤ n := by exact_mod_cast hwn
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (show 1 ≤ n by exact (le_max_left _ _).trans hn)
  have hLn : 4 * L ≤ gamma * (n : ℝ) := by
    have hceil : 4 * L / gamma ≤ (n : ℝ) :=
      (Nat.le_ceil (4 * L / gamma)).trans
        (by exact_mod_cast (le_max_right 1 ⌈4 * L / gamma⌉₊).trans hn)
    have := (div_le_iff₀ hgamma).mp hceil
    nlinarith
  have hlinear : L * (w : ℝ) ≤ gamma / 4 * w * n := by
    nlinarith
  have hlog0 : 0 ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_nonneg (by linarith)
  have hsqrt0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsquare := (sq_le_sq₀
    (mul_nonneg (Real.sqrt_nonneg C) hlog0)
    (mul_nonneg hdelta.le hsqrt0)).2 hlog
  have hsquare' :
      (Real.sqrt C * Real.log ((n : ℝ) + 2)) ^ 2 ≤
        delta ^ 2 * (Real.sqrt (n : ℝ)) ^ 2 := by
    simpa [mul_pow] using hsquare
  have hsqrtC : (Real.sqrt C) ^ 2 = C := Real.sq_sqrt hC
  have hsqrtN : (Real.sqrt (n : ℝ)) ^ 2 = n := Real.sq_sqrt (by positivity)
  have hdeltaSq : delta ^ 2 = gamma / 4 := by
    dsimp [delta]
    rw [Real.sq_sqrt hquarter.le]
  rw [mul_pow, hsqrtC, hdeltaSq, hsqrtN] at hsquare'
  have hlogsq : C * Real.log ((n : ℝ) + 2) ^ 2 ≤ gamma / 4 * n := by
    simpa only [mul_assoc] using hsquare'
  have hlogwidth :
      C * (w : ℝ) * Real.log ((n : ℝ) + 2) ^ 2 ≤
        gamma / 4 * w * n := by
    nlinarith [mul_le_mul_of_nonneg_left hlogsq hw0]
  have hpoint (i : ι w) :
      D w i (n - w) / A w i ≤
        K * (2 : ℝ) ^ (gamma / 2 * w * n) := by
    have hnum := hentry n w hw i
    have hexponent :
        L * (w : ℝ) + C * (w : ℝ) * Real.log ((n : ℝ) + 2) ^ 2 ≤
          gamma / 2 * w * n := by
      linarith
    exact (div_le_self (hD w i (n - w)) (hA w i)).trans
      (hnum.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent) hK))
  calc
    (∑ i : ι w, D w i (n - w) / A w i) ≤
        ∑ _i : ι w, K * (2 : ℝ) ^ (gamma / 2 * w * n) :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    _ = (Nat.card (ι w) : ℝ) *
        (K * (2 : ℝ) ^ (gamma / 2 * w * n)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Nat.card_eq_fintype_card]
    _ ≤ (B * (2 : ℝ) ^ (gamma / 4 * (w : ℝ) ^ 2)) *
        (K * (2 : ℝ) ^ (gamma / 2 * w * n)) :=
      mul_le_mul_of_nonneg_right (hcount w) (by positivity)
    _ = (B * K) *
        ((2 : ℝ) ^ (gamma / 4 * (w : ℝ) ^ 2) *
          (2 : ℝ) ^ (gamma / 2 * w * n)) := by ring
    _ = (B * K) *
        (2 : ℝ) ^
          (gamma / 4 * (w : ℝ) ^ 2 + gamma / 2 * w * n) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ ≤ (2 : ℝ) ^ (gamma / 4 * n) *
        (2 : ℝ) ^
          (gamma / 4 * (w : ℝ) ^ 2 + gamma / 2 * w * n) :=
      mul_le_mul_of_nonneg_right hconst (by positivity)
    _ = (2 : ℝ) ^
        (gamma / 4 * n + gamma / 4 * (w : ℝ) ^ 2 +
          gamma / 2 * w * n) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    _ ≤ (2 : ℝ) ^ (gamma * w * n) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
        nlinarith [mul_nonneg (sub_nonneg.mpr hw1) (by positivity : (0 : ℝ) ≤ n),
          mul_nonneg hw0 (sub_nonneg.mpr (sub_nonneg.mpr hwnR))])

end SymmetricSubgroupAsymptotics

end
