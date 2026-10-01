import SymmetricSubgroupAsymptotics.MarkedC4BoundedWordAssembly
import SymmetricSubgroupAsymptotics.MarkedC4ProductEncoding

/-!
# Assembly of the RDT structural inputs into the global marked moment

This is the formal boundary with Roney-Dougal--Tracey.  The input below does
not contain the global marked moment.  It retains exactly three structural
outputs of the cited proof:

1. Proposition 7.4's bounded binary-word partition into the Case-I total and
   Case-II peel totals.  The marked estimates for those rows were proved in
   the preceding files and are packaged as `BoundedWordCaseDecomposition`.
2. Lemma 2.7, Theorem 7 and Lemma 8.5's fixed-cutoff encodings, after applying
   the generic relative-generator and product-encoding theorems.  Their exact
   cost is a `MarkedMomentReduction` with a proved negligible error.
3. Proposition 6.2, Theorem 6.4 and Theorem 8.6's large-orbit encoding.  For
   every requested positive loss it selects a fixed cutoff and supplies that
   loss before the fixed-cutoff estimate is used.

The first two items can be built from the literal unmarked encodings via
`PermutationRelativeGeneratorEncoding.homMoment_sum_le` and
`ProductEncoding.homMoment_sum_le`; they are not asymptotic assumptions.  The
third item is the quantitative statement of the published large-orbit
reduction.  The theorem below performs every remaining marked and epsilon
calculation and exports the exact proposition consumed by F20.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace MarkedC4

/-- Precise RDT structural data needed by the marked `C4` proof. -/
structure RDTMarkedC4ReductionInput where
  oneGenerator : RDTOneGeneratorSolubleInput
  boundedWordCount : ℕ → ℕ → ℕ → ℝ
  boundedWordCases : ∀ C,
    BoundedWordCaseDecomposition (boundedWordCount C)
  smallSourceCount : ℕ → ℕ → ℕ → ℝ
  fixedCutoff : ∀ C,
    MarkedMomentReduction (smallSourceCount C) (boundedWordCount C)
  largeOrbit : ∀ δ : ℝ, 0 < δ → ∀ K : ℝ,
    ∃ C : ℕ, ∀ᶠ b : ℕ in atTop, ∀ r : ℕ, (r : ℝ) ≤ K * b →
      solubleMarkedC4Moment b r ≤
        (2 : ℝ) ^ (δ * ((b : ℝ) + r) ^ 2) * smallSourceCount C b r

namespace RDTMarkedC4ReductionInput

variable (D : RDTMarkedC4ReductionInput)

/-- The local Case-I/Case-II proof gives the bounded-word main term with its
explicit logarithmic error. -/
theorem boundedWord_errorBound (C : ℕ) :
    MarkedMomentErrorBound (D.boundedWordCount C)
      (boundedWordError (D.boundedWordCases C).A) := by
  intro b r
  simpa only [boundedWordError] using
    (D.boundedWordCases C).count_le_explicit b r

/-- A fixed cutoff has the marked quadratic with a uniform negligible error.
-/
theorem smallSource_bound (C : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∀ K : ℝ, ∀ᶠ b : ℕ in atTop, ∀ r : ℕ,
      (r : ℝ) ≤ K * b →
      D.smallSourceCount C b r ≤
        (2 : ℝ) ^ (markedF b r + ε * ((b : ℝ) + r) ^ 2) := by
  let e : ℕ → ℕ → ℝ := fun b r =>
    (D.fixedCutoff C).error b r + boundedWordError (D.boundedWordCases C).A b r
  have he : UniformQuadraticNegligible e :=
    (D.fixedCutoff C).negligible.add
      (boundedWordError_negligible (D.boundedWordCases C).A_nonneg)
  have hb : MarkedMomentErrorBound (D.smallSourceCount C) e :=
    (D.fixedCutoff C).errorBound (D.boundedWord_errorBound C)
  exact markedMomentBound_of_error hb he

/-- The published large-orbit reduction and the fixed-cutoff proof give the
complete soluble marked moment. -/
theorem solubleGlobalMarkedC4MomentBound
    (R : RDTMarkedC4ReductionInput) :
    SolubleGlobalMarkedC4MomentBound := by
  intro ε hε K
  have hthird : 0 < ε / 3 := by positivity
  obtain ⟨C, hlarge⟩ := R.largeOrbit (ε / 3) hthird K
  filter_upwards [hlarge, R.smallSource_bound C (ε / 3) hthird K]
      with b hlargeb hsmallb
  intro r hr
  have hlargebr := hlargeb r hr
  have hsmallbr := hsmallb r hr
  calc
    solubleMarkedC4Moment b r ≤
        (2 : ℝ) ^ ((ε / 3) * ((b : ℝ) + r) ^ 2) *
          R.smallSourceCount C b r := hlargebr
    _ ≤ (2 : ℝ) ^ ((ε / 3) * ((b : ℝ) + r) ^ 2) *
          (2 : ℝ) ^ (markedF b r +
            (ε / 3) * ((b : ℝ) + r) ^ 2) :=
      mul_le_mul_of_nonneg_left hsmallbr (by positivity)
    _ ≤ (2 : ℝ) ^ (markedF b r + ε * ((b : ℝ) + r) ^ 2) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hsquare : 0 ≤ ((b : ℝ) + r) ^ 2 := sq_nonneg _
      nlinarith

/-- **The full global marked `C4` moment**, derived from the cited RDT
structural data and the project-owned retained-column proof. -/
theorem globalMarkedC4MomentBound
    (R : RDTMarkedC4ReductionInput) :
    Non2UnipotentPrefixFiniteMenu.GlobalMarkedC4MomentBound :=
  globalMarkedC4MomentBound_of_soluble R.oneGenerator
    R.solubleGlobalMarkedC4MomentBound

end RDTMarkedC4ReductionInput

end MarkedC4
end SymmetricSubgroupAsymptotics

end
