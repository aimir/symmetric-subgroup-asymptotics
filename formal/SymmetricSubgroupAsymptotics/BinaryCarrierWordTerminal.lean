import SymmetricSubgroupAsymptotics.BinaryCarrierWordOrderBound
import SymmetricSubgroupAsymptotics.BinaryMarkedTerminalAttachment

/-! Apply the proved whole-word bound after exactly one terminal attachment.
Both terminal marks refer to the same literal carrier subgroup. The full
terminal rectangle, original axis weights and quotient histories remain.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierWord

attribute [local instance] Fintype.ofFinite

open BinaryMarkedGoursatPeel BinaryMarkedTerminalAttachment

/-- A complete actual word followed by one original terminal family.
Only factor orders and nonnegative factored axis weights are assumed.
This theorem does not assert finite carrier coverage or owner acceptance. -/
theorem terminal_weighted_subfamilies_le_history
    {ι : Type} [Fintype ι] (a : ℕ) (s : ι → Bool)
    (w : List Factor) (b : ℕ) (hb : OrderBound w b)
    (v : AxisWeights w) (hv : WeightsNonnegative w v)
    (P : ∀ H : Family w, Subgroup (CriticalProductGroup a s × H.1) → Prop) :
    (∑ H : Family w, weight w v H *
      (Nat.card {K : TerminalActualSubgroups a s H.1 // P H K.1} : ℝ)) ≤
      ∑ j ∈ Finset.range (criticalProductRank a s+1),
        ∑ ell ∈ Finset.range (Fintype.card ι+1),
          coefficient (criticalProductRank a s) (Fintype.card ι) j ell *
            ((((binaryStructuredOrderConstant b *
              (b*w.length+2)^(binaryStructuredOrderConstant b) : ℕ) : ℝ)^w.length) *
              normalHistorySum w v ((j : ℝ)-ell) 0 ell) := by
  refine (weighted_subfamilies_le_markSums a s
    (fun H : Family w => H.1) P (weight w v) (weight_nonneg w v hv)).trans ?_
  apply Finset.sum_le_sum
  intro j hj
  apply Finset.sum_le_sum
  intro ell hell
  have hell' : ell ≤ Fintype.card ι := by simpa using hell
  apply mul_le_mul_of_nonneg_left _ (coefficient_nonneg _ _ _ _ hell')
  have h := markedSum_le_history_of_orderBound w b hb v hv (fun _ => True)
    ((j : ℝ)-ell) 0 ell le_rfl (Nat.cast_nonneg ell)
  simpa only [markedSum,if_true] using h

end SymmetricSubgroupAsymptotics.BinaryCarrierWord
