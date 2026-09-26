import SymmetricSubgroupAsymptotics.BinaryCarrierWordBound
import SymmetricSubgroupAsymptotics.BinaryCarrierWordOrder

/-! Install the complete word bound from a single actual factor-order cap.
The polynomial constant is proved uniformly for all original normal axes;
the history still contains their exact quotient slopes and original weights.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierWord

theorem targetConstants_of_orderBound (w : List Factor) (a : ℕ)
    (ha : OrderBound w a) : TargetConstants w (binaryStructuredOrderConstant a) := by
  induction w with
  | nil => trivial
  | cons A w ih =>
      refine ⟨?_, ih ha.2⟩
      intro N
      exact binaryStructuredQuotientConstant_le_orderConstant A.Carrier N.1 a ha.1

/-- A full original carrier family, with no supplied count, recurrence or
target-constant premise. The explicit polynomial loss depends only on the
order cap and word length. Negative first marks are still permitted. -/
theorem markedSum_le_history_of_orderBound
    (w : List Factor) (a : ℕ) (ha : OrderBound w a)
    (v : AxisWeights w) (hv : WeightsNonnegative w v)
    (P : Subgroup (Product w) → Prop) (x y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    markedSum w v P x y z ≤
      (((binaryStructuredOrderConstant a *
          (a*w.length+2)^(binaryStructuredOrderConstant a) : ℕ) : ℝ)^w.length) *
        normalHistorySum w v x y z :=
  markedSum_le_history w v hv P (a*w.length) (binaryStructuredOrderConstant a)
    (product_card_le_orderBound w a ha) (targetConstants_of_orderBound w a ha)
    x y z hy hz

end SymmetricSubgroupAsymptotics.BinaryCarrierWord
