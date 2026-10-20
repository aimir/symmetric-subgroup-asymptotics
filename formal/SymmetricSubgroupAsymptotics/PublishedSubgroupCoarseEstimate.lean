import SymmetricSubgroupAsymptotics.MarkedC4OrdinarySubgroupUpper
import SymmetricSubgroupAsymptotics.FusionHot

/-! The asymptotic coarse input follows from the quantitative published
Roney-Dougal--Tracey Theorem 1 already used by the marked convolution. -/
set_option autoImplicit false
noncomputable section
open Filter
namespace SymmetricSubgroupAsymptotics

/-- No additional subgroup-count assumption is needed for hot decay. -/
theorem fusionCoarseEstimate_of_published_theorem_one
    (h : MarkedC4.OrdinarySubgroupUpper.PublishedTheoremOneUpper) :
    FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)) := by
  obtain ⟨β, hβ⟩ := h
  intro ε hε
  filter_upwards [eventually_ge_atTop (max 2 ⌈(max β 0 / ε)^2⌉₊)] with n hn
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hb : (max β 0 / ε)^2 ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hn)
  have hs : max β 0 / ε ≤ Real.sqrt (n : ℝ) :=
    (Real.le_sqrt (div_nonneg (le_max_right _ _) hε.le) hn0).mpr hb
  have hβε : β ≤ ε * Real.sqrt (n : ℝ) :=
    (le_max_left β 0).trans (by
      have hh := (div_le_iff₀ hε).mp hs
      simpa only [mul_comm] using hh)
  have herr := mul_le_mul_of_nonneg_right hβε
    (mul_nonneg hn0 (Real.sqrt_nonneg (n : ℝ)))
  have hsq := Real.sq_sqrt hn0
  have hexp : (n : ℝ)^2 / 16 + β*n*Real.sqrt n ≤
      (1/16+ε)*(n : ℝ)^2 := by
    have hsqn := congrArg (fun x : ℝ => ε * (n : ℝ) * x) hsq
    nlinarith only [herr, hsqn]
  change (Nat.card (Subgroup (Equiv.Perm (Fin n))) : ℝ) ≤ _
  exact (hβ n hn2).trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)

end SymmetricSubgroupAsymptotics
