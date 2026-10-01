import SymmetricSubgroupAsymptotics.MarkedC4PermutationEncoding
import SymmetricSubgroupAsymptotics.MarkedC4GlobalReduction

/-!
# Uniform error calculus for the marked moment reductions

The RDT reduction is a finite chain of explicit encodings.  Each encoding has
an exact multiplicative cost; after taking base-two logarithms its cost is
uniformly `o((b+r)^2)` for `r/b` bounded.  This file isolates that calculus so
the structural interfaces never need to state a marked asymptotic theorem.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace MarkedC4

/-- A two-variable error is uniformly quadratically negligible in every
bounded `r/b` window. -/
def UniformQuadraticNegligible (e : ℕ → ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ K : ℝ, ∀ᶠ b : ℕ in atTop, ∀ r : ℕ,
    (r : ℝ) ≤ K * b → e b r ≤ ε * ((b : ℝ) + r) ^ 2

theorem uniformQuadraticNegligible_zero :
    UniformQuadraticNegligible (fun _ _ => 0) := by
  intro ε hε K
  filter_upwards [] with b
  intro r hr
  positivity

theorem UniformQuadraticNegligible.add
    {e₁ e₂ : ℕ → ℕ → ℝ}
    (h₁ : UniformQuadraticNegligible e₁)
    (h₂ : UniformQuadraticNegligible e₂) :
    UniformQuadraticNegligible (fun b r => e₁ b r + e₂ b r) := by
  intro ε hε K
  have hhalf : 0 < ε / 2 := by positivity
  filter_upwards [h₁ (ε / 2) hhalf K, h₂ (ε / 2) hhalf K]
      with b h₁b h₂b
  intro r hr
  have hleft := h₁b r hr
  have hright := h₂b r hr
  linarith

theorem UniformQuadraticNegligible.mono
    {e₁ e₂ : ℕ → ℕ → ℝ}
    (h₁ : UniformQuadraticNegligible e₁)
    (hle : ∀ b r, e₂ b r ≤ e₁ b r) :
    UniformQuadraticNegligible e₂ := by
  intro ε hε K
  filter_upwards [h₁ ε hε K] with b hb
  intro r hr
  exact (hle b r).trans (hb r hr)

/-- A count has the marked quadratic with an explicit error. -/
def MarkedMomentErrorBound (count : ℕ → ℕ → ℝ)
    (e : ℕ → ℕ → ℝ) : Prop :=
  ∀ b r, count b r ≤ (2 : ℝ) ^ (markedF b r + e b r)

/-- An explicit negligible error gives the uniform epsilon formulation. -/
theorem markedMomentBound_of_error
    {count : ℕ → ℕ → ℝ} {e : ℕ → ℕ → ℝ}
    (hbound : MarkedMomentErrorBound count e)
    (hnegligible : UniformQuadraticNegligible e) :
    ∀ ε : ℝ, 0 < ε → ∀ K : ℝ, ∀ᶠ b : ℕ in atTop, ∀ r : ℕ,
      (r : ℝ) ≤ K * b →
      count b r ≤ (2 : ℝ) ^
        (markedF b r + ε * ((b : ℝ) + r) ^ 2) := by
  intro ε hε K
  filter_upwards [hnegligible ε hε K] with b hb
  intro r hr
  exact (hbound b r).trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by simpa [add_comm] using add_le_add_left (hb r hr) (markedF b r)))

/-- A pointwise multiplicative reduction, written in exponent form. -/
structure MarkedMomentReduction
    (source target : ℕ → ℕ → ℝ) where
  error : ℕ → ℕ → ℝ
  error_nonneg : ∀ b r, 0 ≤ error b r
  negligible : UniformQuadraticNegligible error
  bound : ∀ b r, source b r ≤ (2 : ℝ) ^ (error b r) * target b r

namespace MarkedMomentReduction

variable {source middle target : ℕ → ℕ → ℝ}

/-- Compose two literal weighted encodings. -/
noncomputable def trans
    (R₁ : MarkedMomentReduction source middle)
    (R₂ : MarkedMomentReduction middle target) :
    MarkedMomentReduction source target where
  error := fun b r => R₁.error b r + R₂.error b r
  error_nonneg := fun b r => add_nonneg (R₁.error_nonneg b r) (R₂.error_nonneg b r)
  negligible := R₁.negligible.add R₂.negligible
  bound := by
    intro b r
    calc
      source b r ≤ (2 : ℝ) ^ R₁.error b r * middle b r := R₁.bound b r
      _ ≤ (2 : ℝ) ^ R₁.error b r *
          ((2 : ℝ) ^ R₂.error b r * target b r) :=
        mul_le_mul_of_nonneg_left (R₂.bound b r) (by positivity)
      _ = (2 : ℝ) ^ (R₁.error b r + R₂.error b r) * target b r := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        ring

/-- Transport an explicit marked main-term bound through a reduction. -/
theorem errorBound
    (R : MarkedMomentReduction source target)
    {e : ℕ → ℕ → ℝ}
    (htarget : MarkedMomentErrorBound target e) :
    MarkedMomentErrorBound source (fun b r => R.error b r + e b r) := by
  intro b r
  calc
    source b r ≤ (2 : ℝ) ^ R.error b r * target b r := R.bound b r
    _ ≤ (2 : ℝ) ^ R.error b r *
        (2 : ℝ) ^ (markedF b r + e b r) :=
      mul_le_mul_of_nonneg_left (htarget b r) (by positivity)
    _ = (2 : ℝ) ^ (markedF b r + (R.error b r + e b r)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

end MarkedMomentReduction

end MarkedC4
end SymmetricSubgroupAsymptotics

end
