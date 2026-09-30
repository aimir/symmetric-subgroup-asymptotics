import SymmetricSubgroupAsymptotics.GrowingMenuMassCertificate

/-!
# Aggregating a growing menu from index and entry bounds

This file separates the two inputs which normally prove a concrete menu-mass
certificate: a subquadratic bound for the number of indices at a fixed width,
and a polynomial/subquadratic bound for each individual weighted entry.  The
result keeps the ambient-degree polynomial and adds the two width exponents.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {ι : ℕ → Type*} [∀ w, Fintype (ι w)]

/-- The number of width-`w` menu indices is subquadratic on the logarithmic
scale.  A fixed multiplicative constant is allowed so finite widths can be
absorbed without changing the statement. -/
def SubquadraticMenuIndexCount (ι : ℕ → Type*) [∀ w, Fintype (ι w)] : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w,
      (Nat.card (ι w) : ℝ) ≤ B * (2 : ℝ) ^ (ε * (w : ℝ) ^ 2)

/-- Every individual original-weight entry has a polynomial ambient cost and
an arbitrarily small quadratic width cost.  The constants are uniform in the
index, width, complement degree, and ambient degree. -/
def PolynomialSubquadraticMenuEntryBound (w₀ : ℕ)
    (D : ∀ w, ι w → ℕ → ℝ) (A : ∀ w, ι w → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ B : ℝ, ∃ p : ℕ, 0 ≤ B ∧
      ∀ n w, w ∈ Finset.Ico w₀ (n + 1) → ∀ i,
        D w i (n - w) / A w i ≤
          B * (((n + 1 : ℕ) : ℝ) ^ p) *
            (2 : ℝ) ^ (ε * (w : ℝ) ^ 2)

/-- The corresponding bound before division by the original weight.  This is
often the form produced directly by an incidence calculation. -/
def PolynomialSubquadraticMenuNumeratorBound (w₀ : ℕ)
    (D : ∀ w, ι w → ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ B : ℝ, ∃ p : ℕ, 0 ≤ B ∧
      ∀ n w, w ∈ Finset.Ico w₀ (n + 1) → ∀ i,
        D w i (n - w) ≤
          B * (((n + 1 : ℕ) : ℝ) ^ p) *
            (2 : ℝ) ^ (ε * (w : ℝ) ^ 2)

omit [∀ w, Fintype (ι w)] in
/-- A nonnegative numerator bound implies the weighted entry bound whenever
the original divisor is at least one.  Thus retaining a normalizer can never
make the menu aggregation harder. -/
theorem polynomialSubquadraticMenuEntryBound_of_numerator
    {w₀ : ℕ} (D : ∀ w, ι w → ℕ → ℝ) (A : ∀ w, ι w → ℝ)
    (hD : ∀ w i b, 0 ≤ D w i b) (hA : ∀ w i, 1 ≤ A w i)
    (hnum : PolynomialSubquadraticMenuNumeratorBound w₀ D) :
    PolynomialSubquadraticMenuEntryBound w₀ D A := by
  intro ε hε
  obtain ⟨B, p, hB, hbound⟩ := hnum ε hε
  refine ⟨B, p, hB, ?_⟩
  intro n w hw i
  exact (div_le_self (hD w i (n - w)) (hA w i)).trans
    (hbound n w hw i)

/-- A subquadratic index count times a uniform subquadratic entry bound gives
the complete polynomial/subquadratic menu-mass certificate. -/
theorem polynomialSubquadraticMenuMassBound_of_index_entry
    {w₀ : ℕ} (D : ∀ w, ι w → ℕ → ℝ) (A : ∀ w, ι w → ℝ)
    (hindex : SubquadraticMenuIndexCount ι)
    (hentry : PolynomialSubquadraticMenuEntryBound w₀ D A) :
    PolynomialSubquadraticMenuMassBound w₀ D A := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨Bι, hBι, hι⟩ := hindex (ε / 2) hhalf
  obtain ⟨BD, p, hBD, hD⟩ := hentry (ε / 2) hhalf
  refine ⟨Bι * BD, p, mul_nonneg hBι hBD, ?_⟩
  intro n w hw
  let E : ℝ := BD * (((n + 1 : ℕ) : ℝ) ^ p) *
    (2 : ℝ) ^ ((ε / 2) * (w : ℝ) ^ 2)
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  calc
    (∑ i, D w i (n - w) / A w i) ≤ ∑ _i : ι w, E :=
      Finset.sum_le_sum (fun i _ => hD n w hw i)
    _ = (Nat.card (ι w) : ℝ) * E := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Nat.card_eq_fintype_card]
    _ ≤ (Bι * (2 : ℝ) ^ ((ε / 2) * (w : ℝ) ^ 2)) * E :=
      mul_le_mul_of_nonneg_right (hι w) hE
    _ = (Bι * BD) * (((n + 1 : ℕ) : ℝ) ^ p) *
        (2 : ℝ) ^ (ε * (w : ℝ) ^ 2) := by
      dsimp [E]
      calc
        _ = (Bι * BD) * (((n + 1 : ℕ) : ℝ) ^ p) *
            ((2 : ℝ) ^ ((ε / 2) * (w : ℝ) ^ 2) *
              (2 : ℝ) ^ ((ε / 2) * (w : ℝ) ^ 2)) := by ring_nf
        _ = _ := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1
          ring_nf

end SymmetricSubgroupAsymptotics

end
