import SymmetricSubgroupAsymptotics.TerminalAttachmentBound
import SymmetricSubgroupAsymptotics.TerminalEstimates

/-! Uniform physical terminal estimates, retaining original exterior weights. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics

variable {ι : Type} [Fintype ι] (a : ℕ) (s : ι → Bool)
  (T : Type) [Group T] [Finite T]

/-- Uniform physical ratio with every relation dimension retained. -/
theorem terminalActualSubgroups_ratio_le :
    (Nat.card (TerminalActualSubgroups a s T) : ℝ) /
        terminalGaussianWeight (criticalProductRank a s) (binaryCharacterRank T) ≤
      2 * (eulerProduct⁻¹)^3 * (criticalProductRank a s+1) *
        ∑ l ∈ Finset.range (Fintype.card ι+1),
          terminalRelationWeight (criticalProductRank a s) (Fintype.card ι)
            (binaryCharacterRank T) (Module.finrank (ZMod 2) (terminalRestrictedInflationKernel T)) l :=
  (div_le_div_of_nonneg_right (terminalActualSubgroups_card_le_doubleSum a s T)
    (terminalGaussianWeight_pos _ _).le).trans (terminalGaussianDoubleSum_div_le _ _ _ _)

/-- In the large-exterior endpoint the stronger suppression is retained,
rather than replacing it by the interior deficit. -/
theorem terminalActualSubgroups_endpoint_ratio_le
    (hd : criticalProductRank a s ≤ binaryCharacterRank T) :
    (Nat.card (TerminalActualSubgroups a s T) : ℝ) /
        terminalGaussianWeight (criticalProductRank a s) (binaryCharacterRank T) ≤
      (eulerProduct⁻¹)^3 * (criticalProductRank a s+1) *
        ∑ l ∈ Finset.range (Fintype.card ι+1),
          terminalEndpointRelationWeight (Fintype.card ι) (binaryCharacterRank T)
            (Module.finrank (ZMod 2) (terminalRestrictedInflationKernel T)) l :=
  (div_le_div_of_nonneg_right (terminalActualSubgroups_card_le_doubleSum a s T)
    (terminalGaussianWeight_pos _ _).le).trans (terminalGaussianDoubleSum_endpoint_div_le _ _ _ _ hd)

/-- The convergent relation series bounds the actual complete exterior
attachment, with the actual retained inflation dimension. -/
theorem terminalActualSubgroups_ratio_le_series :
    (Nat.card (TerminalActualSubgroups a s T) : ℝ) /
        terminalGaussianWeight (criticalProductRank a s) (binaryCharacterRank T) ≤
      2 * (eulerProduct⁻¹)^3 * (criticalProductRank a s+1) *
        ∑' l : ℕ, terminalRelationKernel
          ((criticalProductRank a s : ℝ)/2-Fintype.card ι+(binaryCharacterRank T : ℝ)/2-
            Module.finrank (ZMod 2) (terminalRestrictedInflationKernel T)) l :=
  (div_le_div_of_nonneg_right (terminalActualSubgroups_card_le_doubleSum a s T)
    (terminalGaussianWeight_pos _ _).le).trans (terminalGaussianDoubleSum_div_le_series _ _ _ _)

/-- A trivial actual inflation kernel gives one absolute terminal constant,
uniformly in every exterior rank and every zero-dimensional boundary case. -/
theorem terminalActualSubgroups_zero_inflation_le
    (hτ : terminalRestrictedInflationKernel T=⊥) :
    (Nat.card (TerminalActualSubgroups a s T) : ℝ) ≤
      ((2 : ℝ)^(66 : ℕ) * (eulerProduct⁻¹)^3) * (criticalProductRank a s+1) *
        terminalGaussianWeight (criticalProductRank a s) (binaryCharacterRank T) := by
  have h := terminalActualSubgroups_card_le_doubleSum a s T
  rw [hτ,finrank_bot] at h
  exact h.trans (terminalGaussianDoubleSum_zero_inflation_le _ _ _
    (terminalCritical_two_card_le_rank a s))

/-- Any nonnegative original labels or normalizer weights can be summed
without replacing the complete exterior or any original critical profile. -/
theorem terminalActualSubgroups_weighted_sum_le_doubleSum
    {J : Type} [Fintype J] (I : J → Type) [∀ j, Fintype (I j)]
    (a : J → ℕ) (s : ∀ j, I j → Bool) (T : J → Type)
    [∀ j, Group (T j)] [∀ j, Finite (T j)] (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) :
    (∑ j, w j * (Nat.card (TerminalActualSubgroups (a j) (s j) (T j)) : ℝ)) ≤
      ∑ j, w j * terminalGaussianDoubleSum (criticalProductRank (a j) (s j))
        (Fintype.card (I j)) (binaryCharacterRank (T j))
          (Module.finrank (ZMod 2) (terminalRestrictedInflationKernel (T j))) := by
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left
    (terminalActualSubgroups_card_le_doubleSum (a j) (s j) (T j)) (hw j)

/-- With trivial original inflation kernels the same original nonnegative
weights remain inside the Gaussian attachment sum. -/
theorem terminalActualSubgroups_weighted_zero_inflation_le
    {J : Type} [Fintype J] (I : J → Type) [∀ j, Fintype (I j)]
    (a : J → ℕ) (s : ∀ j, I j → Bool) (T : J → Type)
    [∀ j, Group (T j)] [∀ j, Finite (T j)] (w : J → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hτ : ∀ j, terminalRestrictedInflationKernel (T j)=⊥) :
    (∑ j, w j * (Nat.card (TerminalActualSubgroups (a j) (s j) (T j)) : ℝ)) ≤
      ((2 : ℝ)^(66 : ℕ) * (eulerProduct⁻¹)^3) *
        ∑ j, w j * (criticalProductRank (a j) (s j)+1) *
          terminalGaussianWeight (criticalProductRank (a j) (s j)) (binaryCharacterRank (T j)) := by
  calc
    _ ≤ ∑ j, w j * (((2 : ℝ)^(66 : ℕ) * (eulerProduct⁻¹)^3) *
        (criticalProductRank (a j) (s j)+1) *
          terminalGaussianWeight (criticalProductRank (a j) (s j)) (binaryCharacterRank (T j))) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (terminalActualSubgroups_zero_inflation_le (a j) (s j) (T j) (hτ j)) (hw j)
    _ = _ := by simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring

end SymmetricSubgroupAsymptotics

