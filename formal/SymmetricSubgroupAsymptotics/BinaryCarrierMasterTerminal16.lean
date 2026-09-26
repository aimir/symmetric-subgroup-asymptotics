import SymmetricSubgroupAsymptotics.BinaryCarrierMasterWords16
import SymmetricSubgroupAsymptotics.BinaryCarrierUnitWeights
import SymmetricSubgroupAsymptotics.BinaryCarrierWordTerminalEnergy

/-! One terminal attachment to each complete original degree-sixteen
master word. Unit normal weights discharge the internal normal-history
multiplicity. Any original action-normalizer/profile factor remains outside
this fixed-word count; no owner coverage or profile summation is asserted.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierMasterWords16

open BinaryCarrierWord

attribute [local instance] Fintype.ofFinite

/-- A fixed original word has at most this many literal normal histories.
Repeated original factors retain separate normal choices. -/
theorem unit_axisWeightProduct_le (masters : List Master) :
    axisWeightProduct (word masters) (unitAxisWeights (word masters)) ≤
      (2 : ℝ)^(4096*masters.length) := by
  simpa only [word_length, show (2 : ℕ)^12 = 4096 from rfl] using
    axisWeightProduct_unitAxisWeights_le_of_orderBound
      (word masters) 12 (orderBound masters)

/-- Attach the terminal product exactly once to each actual full carrier.
All terminal survival tests may be retained. The finite normal multiplicity
is proved from the original order bound, with no weight hypothesis.
-/
theorem terminal_subfamilies_le_reserve
    {ι : Type} [Fintype ι] (a : ℕ) (s : ι → Bool)
    (masters : List Master)
    (P : ∀ H : Family (word masters),
      Subgroup (CriticalProductGroup a s × H.1) → Prop) :
    (∑ H : Family (word masters),
      (Nat.card {K : TerminalActualSubgroups a s H.1 // P H K.1} : ℝ)) ≤
      (((binaryStructuredOrderConstant 12 *
        (12*masters.length+2)^(binaryStructuredOrderConstant 12) : ℕ) : ℝ)^masters.length) *
        (((eulerProduct⁻¹)^3 * ((criticalProductRank a s+1 : ℕ) : ℝ) *
          (∑ ell ∈ Finset.range (Fintype.card ι+1), (72 : ℝ)^ell)) *
            ((2 : ℝ)^(4096*masters.length) *
              (2 : ℝ)^(((criticalProductRank a s : ℝ)+4*(2*(masters.length : ℝ)))^2/4 -
                (25/82)*(criticalProductRank a s)*(2*(masters.length : ℝ)) -
                (29/164)*(2*(masters.length : ℝ))^2))) := by
  have h := BinaryCarrierWord.terminal_weighted_subfamilies_le_reserve
    a s (word masters) 12 (orderBound masters)
    (unitAxisWeights (word masters)) (unitAxisWeights_nonnegative (word masters))
    P (2*(masters.length : ℝ)) (certifiedHistoryRows masters)
  simp only [weight_unitAxisWeights, one_mul, word_length] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) _)
  apply mul_le_mul_of_nonneg_left _ (by positivity [euler_positive])
  exact mul_le_mul_of_nonneg_right (unit_axisWeightProduct_le masters)
    (Real.rpow_nonneg (by norm_num) _)

end SymmetricSubgroupAsymptotics.BinaryCarrierMasterWords16
