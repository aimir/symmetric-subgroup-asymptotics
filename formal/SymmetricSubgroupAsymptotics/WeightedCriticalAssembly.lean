import SymmetricSubgroupAsymptotics.WeightedCounting
import SymmetricSubgroupAsymptotics.CriticalProfileAssembly

/-!
# Original-weight assembly of critical-family estimates

The normalization is derived from the exact cardinality of the literal
labelled subgroup family. All profile weights are retained.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

theorem CriticalProfile.weight_pos (p : CriticalProfile) : 0 < p.weight := by
  unfold CriticalProfile.weight
  positivity

theorem criticalProfile_weight_sum_real (R : ℕ) :
    (∑ p : (criticalProfiles R), (p.1.weight : ℝ)) = (criticalCoefficient R : ℝ) := by
  have h := criticalProfileSum_eq_criticalCoefficient R
  unfold criticalProfileSum at h
  exact_mod_cast (show (∑ p : (criticalProfiles R), p.1.weight) = criticalCoefficient R by
    simpa only [Finset.sum_coe_sort] using h)

theorem evenCriticalSubgroups_card_real (R : ℕ) :
    (Nat.card (EvenCriticalSubgroups R) : ℝ) =
      ((2 * R).factorial : ℝ) *
        ∑ p : (criticalProfiles R), (p.1.weight : ℝ) * Nat.card (CriticalModelSubgroups p.1) := by
  exact_mod_cast evenCriticalSubgroups_card R

/-- Exact cancellation of the labelling factorial against the approved
benchmark leaves the original weighted average of the model counts. -/
theorem evenCriticalSubgroups_normalized (R : ℕ) :
    (Nat.card (EvenCriticalSubgroups R) : ℝ) / exactBenchmark (2 * R) =
      (∑ p : (criticalProfiles R), (p.1.weight : ℝ) * Nat.card (CriticalModelSubgroups p.1)) /
        ((binarySubspaceCount R : ℝ) * (criticalCoefficient R : ℝ)) := by
  have hf : ((2 * R).factorial : ℝ) ≠ 0 := by positivity
  have hG : (binaryGaussianSum R : ℝ) = binarySubspaceCount R := by
    exact_mod_cast (binarySubspaceCount_eq_gaussianSum R).symm
  rw [evenCriticalSubgroups_card_real, exactBenchmark]
  simp only [halfDegree, parityCoefficient, parity, Nat.mul_div_cancel_left _ (by omega : 0 < 2),
    Nat.mul_mod_right, zero_ne_one, false_and, ↓reduceIte, add_zero, hG]
  field_simp

/-- Actual critical subgroups form a subfamily of all labelled subgroups. -/
theorem evenCriticalSubgroups_card_le_subgroupCount (R : ℕ) :
    Nat.card (EvenCriticalSubgroups R) ≤ subgroupCount (2 * R) := by
  exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

/-- A finite original-weight assembly estimate, with the exceptional profile
contribution still explicit. Concrete profile estimates discharge its premise. -/
theorem evenCriticalSubgroups_relative_error_of_profiles (R : ℕ)
    (δ : ℝ) (ε : CriticalProfile → ℝ)
    (herror : ∀ p ∈ criticalProfiles R,
      |(Nat.card (CriticalModelSubgroups p) : ℝ) / binarySubspaceCount R - 1| ≤ δ + ε p) :
    |(Nat.card (EvenCriticalSubgroups R) : ℝ) / exactBenchmark (2 * R) - 1| ≤
      δ + (∑ p : (criticalProfiles R), (p.1.weight : ℝ) * ε p.1) /
        (criticalCoefficient R : ℝ) := by
  have h := finite_weighted_relative_error
    (fun p : (criticalProfiles R) ↦ (p.1.weight : ℝ))
    (fun p ↦ (Nat.card (CriticalModelSubgroups p.1) : ℝ))
    (fun p ↦ ε p.1) (binarySubspaceCount R : ℝ) δ
    (fun p ↦ by change (0 : ℝ) ≤ (p.1.weight : ℝ); exact_mod_cast p.1.weight_pos.le)
    (by rw [criticalProfile_weight_sum_real]; exact_mod_cast criticalCoefficient_pos R)
    (by exact_mod_cast binarySubspaceCount_pos R)
    (fun p ↦ herror p.1 p.2)
  simpa only [criticalProfile_weight_sum_real, evenCriticalSubgroups_normalized] using h

end SymmetricSubgroupAsymptotics
