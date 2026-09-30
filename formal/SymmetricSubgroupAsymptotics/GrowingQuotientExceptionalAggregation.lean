import SymmetricSubgroupAsymptotics.GrowingQuotientAdditiveExceptional
import SymmetricSubgroupAsymptotics.FusionShiftedMenu

/-!
# Bounded-width aggregation of exceptional physical rows

Source-summed rank-tail estimates are produced one original action at a
time.  This file performs the only safe global aggregation: if every
exceptional row is zero beyond a fixed original width, then the growing
menu is eventually a finite shifted sum, so cellwise exponential decay
gives one exponential bound for the complete exceptional scalar.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {ι : ℕ → Type*} [∀ w, Fintype (ι w)]

private theorem sum_Ico_subtype_exceptionalAggregation
    {w0 W : ℕ} (f : ℕ → ℝ) :
    (∑ w : {w : ℕ // w ∈ Finset.Ico w0 (W + 1)}, f w.1) =
      ∑ w ∈ Finset.Ico w0 (W + 1), f w := by
  exact (Finset.sum_subtype (Finset.Ico w0 (W + 1))
    (fun _ => Iff.rfl) f).symm

/-- A growing exceptional menu supported on finitely many original widths
inherits exponential decay from its individual action cells. -/
noncomputable def exponentialScalarBound_growingQuotientExceptionalTotal
    (w0 W : ℕ) (X : ∀ w, ι w → ℕ → ℝ)
    (hcell : ∀ w i, ExponentialScalarBound (X w i))
    (hsupport : ∀ w i, W < w → X w i = 0) :
    ExponentialScalarBound (growingQuotientExceptionalTotal w0 X) := by
  let κ := Σ w : {w : ℕ // w ∈ Finset.Ico w0 (W + 1)}, ι w.1
  let f : κ → ℕ → ℝ := fun x => X x.1.1 x.2
  let shift : κ → ℕ := fun x => x.1.1
  have hfinite : ∀ x : κ, ∃ C r : ℝ, 0 < C ∧ 0 < r ∧
      ∀ᶠ b : ℕ in atTop,
        f x b ≤ C * (2 : ℝ) ^ (-r * (b : ℝ) ^ 1) := by
    intro x
    let E := hcell x.1.1 x.2
    refine ⟨E.constant, E.rate, E.constant_pos, E.rate_pos, ?_⟩
    filter_upwards [eventually_ge_atTop E.threshold] with b hb
    simpa only [f, pow_one] using E.bound b hb
  let hshifted := fusion_finite_shifted_decay f shift 1 hfinite
  let C : ℝ := Classical.choose hshifted
  have hCrest := Classical.choose_spec hshifted
  let r : ℝ := Classical.choose hCrest
  have hrest := Classical.choose_spec hCrest
  have hC : 0 < C := hrest.1
  have hr : 0 < r := hrest.2.1
  have hsum : ∀ᶠ n : ℕ in atTop,
      ∑ x : κ, f x (n - shift x) ≤
        C * (2 : ℝ) ^ (-r * (n : ℝ) ^ 1) := hrest.2.2
  let N : ℕ := Classical.choose (eventually_atTop.mp hsum)
  have hN := Classical.choose_spec (eventually_atTop.mp hsum)
  refine
    { threshold := max N W
      rate := r
      constant := C
      rate_pos := hr
      constant_pos := hC
      bound := ?_ }
  intro n hn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnW : W ≤ n := (le_max_right _ _).trans hn
  have hmenu : growingQuotientExceptionalTotal w0 X n =
      ∑ x : κ, f x (n - shift x) := by
    unfold growingQuotientExceptionalTotal
    have hsubset : Finset.Ico w0 (W + 1) ⊆ Finset.Ico w0 (n + 1) := by
      intro w hw
      simp only [Finset.mem_Ico] at hw ⊢
      omega
    calc
      (∑ w ∈ Finset.Ico w0 (n + 1), ∑ i, X w i (n - w)) =
          ∑ w ∈ Finset.Ico w0 (W + 1), ∑ i, X w i (n - w) := by
        symm
        apply Finset.sum_subset hsubset
        intro w hwn hwW
        have hWw : W < w := by
          simp only [Finset.mem_Ico] at hwn
          by_contra hnot
          have : w < W + 1 := by omega
          exact hwW (by
            simp only [Finset.mem_Ico]
            exact ⟨hwn.1, this⟩)
        simp only [hsupport w _ hWw]
        simp
      _ = ∑ w : {w : ℕ // w ∈ Finset.Ico w0 (W + 1)},
          ∑ i, X w.1 i (n - w.1) := by
        exact (sum_Ico_subtype_exceptionalAggregation
          (w0 := w0) (W := W)
          (fun w => ∑ i, X w i (n - w))).symm
      _ = ∑ x : κ, f x (n - shift x) := by
        rw [Fintype.sum_sigma]
  rw [hmenu]
  simpa only [pow_one] using hN n hnN

end SymmetricSubgroupAsymptotics

end
