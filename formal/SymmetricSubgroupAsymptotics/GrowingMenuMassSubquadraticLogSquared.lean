import SymmetricSubgroupAsymptotics.GrowingMenuMassLogSquared

/-!
# Growing menu mass with a subquadratic width coefficient

The affine chief-layer coefficient has two independent finite costs.  The
semisimple outer factors have the familiar `w * log(n + 2)^2` envelope,
while invariant intersections and normal graphs contribute `o(w^2)`.
Neither cost should be forced into the other.  This file proves the exact
combined aggregation used by the affine owner menu.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {ι : ℕ → Type*} [∀ w, Fintype (ι w)]

/-- A uniform entry envelope consisting of an arbitrarily small quadratic
width term and the standard linear/log-squared source term.  Constants may
depend on `epsilon`, but never on the action, width, source degree or ambient
degree. -/
def SubquadraticLinearLogSquaredMenuNumeratorBound (w₀ : ℕ)
    (D : ∀ w, ι w → ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ K L C : ℝ, 0 ≤ K ∧ 0 ≤ L ∧ 0 ≤ C ∧
      ∀ n w, w ∈ Finset.Ico w₀ (n + 1) → ∀ i,
        D w i (n - w) ≤
          K * (2 : ℝ) ^
            (ε * (w : ℝ) ^ 2 + L * w +
              C * w * Real.log ((n : ℝ) + 2) ^ 2)

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

/-- The combined affine coefficient is a valid growing menu mass.  The proof
keeps the action-count, finite constant, quadratic-width, linear-width and
log-squared costs separate until each receives one eighth of the requested
`gamma * w * n` reserve. -/
theorem growingMenuMassBound_of_subquadraticLinearLogSquared
    {w₀ : ℕ} (hw₀ : 1 ≤ w₀)
    (D : ∀ w, ι w → ℕ → ℝ) (A : ∀ w, ι w → ℝ)
    (hD : ∀ w i b, 0 ≤ D w i b)
    (hA : ∀ w i, 1 ≤ A w i)
    (hindex : SubquadraticMenuIndexCount ι)
    (henvelope : SubquadraticLinearLogSquaredMenuNumeratorBound w₀ D) :
    GrowingMenuMassBound w₀ D A := by
  intro gamma hgamma
  let ε : ℝ := gamma / 8
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨B, hB, hcount⟩ := hindex ε hε
  obtain ⟨K, L, C, hK, hL, hC, hentry⟩ := henvelope ε hε
  let delta : ℝ := Real.sqrt ε
  have hdelta : 0 < delta := Real.sqrt_pos.2 hε
  filter_upwards [
      BinaryMixtureNumerics.eventually_log_error_le_sqrt
        (Real.sqrt C) (Real.sqrt_nonneg C) hdelta,
      eventually_const_le_two_rpow (K := B * K) (gamma := ε)
        (mul_nonneg hB hK) hε,
      eventually_ge_atTop (max 1 ⌈L / ε⌉₊)] with n hlog hconst hn
  intro w hw
  have hww := Finset.mem_Ico.mp hw
  have hwn : w ≤ n := by omega
  have hw1N : 1 ≤ w := hw₀.trans hww.1
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw1N
  have hw0 : (0 : ℝ) ≤ w := zero_le_one.trans hw1
  have hwnR : (w : ℝ) ≤ n := by exact_mod_cast hwn
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (show 1 ≤ n by exact (le_max_left _ _).trans hn)
  have hLn : L ≤ ε * (n : ℝ) := by
    have hceil : L / ε ≤ (n : ℝ) :=
      (Nat.le_ceil (L / ε)).trans
        (by exact_mod_cast (le_max_right 1 ⌈L / ε⌉₊).trans hn)
    calc
      L ≤ (n : ℝ) * ε := (div_le_iff₀ hε).mp hceil
      _ = ε * n := by ring
  have hlinear : L * (w : ℝ) ≤ ε * w * n := by
    nlinarith [mul_le_mul_of_nonneg_right hLn hw0]
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
  have hdeltaSq : delta ^ 2 = ε := by
    dsimp [delta]
    rw [Real.sq_sqrt hε.le]
  rw [mul_pow, hsqrtC, hdeltaSq, hsqrtN] at hsquare'
  have hlogsq : C * Real.log ((n : ℝ) + 2) ^ 2 ≤ ε * n := by
    simpa only [mul_assoc] using hsquare'
  have hlogwidth :
      C * (w : ℝ) * Real.log ((n : ℝ) + 2) ^ 2 ≤
        ε * w * n := by
    nlinarith [mul_le_mul_of_nonneg_left hlogsq hw0]
  have hpoint (i : ι w) :
      D w i (n - w) / A w i ≤
        K * (2 : ℝ) ^
          (ε * (w : ℝ) ^ 2 + ε * w * n + ε * w * n) := by
    have hnum := hentry n w hw i
    have hexponent :
        ε * (w : ℝ) ^ 2 + L * w +
            C * w * Real.log ((n : ℝ) + 2) ^ 2 ≤
          ε * (w : ℝ) ^ 2 + ε * w * n + ε * w * n := by
      linarith
    exact (div_le_self (hD w i (n - w)) (hA w i)).trans
      (hnum.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent) hK))
  calc
    (∑ i : ι w, D w i (n - w) / A w i) ≤
        ∑ _i : ι w, K * (2 : ℝ) ^
          (ε * (w : ℝ) ^ 2 + ε * w * n + ε * w * n) :=
      Finset.sum_le_sum (fun i _ ↦ hpoint i)
    _ = (Nat.card (ι w) : ℝ) *
        (K * (2 : ℝ) ^
          (ε * (w : ℝ) ^ 2 + ε * w * n + ε * w * n)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Nat.card_eq_fintype_card]
    _ ≤ (B * (2 : ℝ) ^ (ε * (w : ℝ) ^ 2)) *
        (K * (2 : ℝ) ^
          (ε * (w : ℝ) ^ 2 + ε * w * n + ε * w * n)) :=
      mul_le_mul_of_nonneg_right (hcount w) (by positivity)
    _ = (B * K) * (2 : ℝ) ^
        (ε * (w : ℝ) ^ 2 + ε * (w : ℝ) ^ 2 +
          ε * w * n + ε * w * n) := by
      calc
        _ = (B * K) * ((2 : ℝ) ^ (ε * (w : ℝ) ^ 2) *
            (2 : ℝ) ^
              (ε * (w : ℝ) ^ 2 + ε * w * n + ε * w * n)) := by ring
        _ = (B * K) * (2 : ℝ) ^
            (ε * (w : ℝ) ^ 2 +
              (ε * (w : ℝ) ^ 2 + ε * w * n + ε * w * n)) := by
          congr 1
          exact (Real.rpow_add (by norm_num : (0 : ℝ) < 2)
            (ε * (w : ℝ) ^ 2)
            (ε * (w : ℝ) ^ 2 + ε * w * n + ε * w * n)).symm
        _ = _ := by congr 2 <;> ring
    _ ≤ (2 : ℝ) ^ (ε * n) * (2 : ℝ) ^
        (ε * (w : ℝ) ^ 2 + ε * (w : ℝ) ^ 2 +
          ε * w * n + ε * w * n) :=
      mul_le_mul_of_nonneg_right hconst (by positivity)
    _ = (2 : ℝ) ^
        (ε * n + ε * (w : ℝ) ^ 2 + ε * (w : ℝ) ^ 2 +
          ε * w * n + ε * w * n) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    _ ≤ (2 : ℝ) ^ (gamma * w * n) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
        dsimp [ε]
        have hn0 : (0 : ℝ) ≤ n := by positivity
        nlinarith [mul_nonneg (sub_nonneg.mpr hw1) hn0,
          mul_nonneg hw0 (sub_nonneg.mpr (sub_nonneg.mpr hwnR))])

end SymmetricSubgroupAsymptotics

end
