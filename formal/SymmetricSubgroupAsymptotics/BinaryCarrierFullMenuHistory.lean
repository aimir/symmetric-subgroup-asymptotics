import SymmetricSubgroupAsymptotics.BinaryCarrierFullMenuEnergy
import SymmetricSubgroupAsymptotics.BinaryCarrierWordEffectiveEnvelope

/-! Install the full mixed-scale numerical menu on original normal-axis
histories. Labels are selected separately at each literal position. Their
physical scales have an exact common sum; normal multiplicities and all
axis weights remain those of the original word. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryCarrierFullMenuHistory

open BinaryCarrierWord BinaryCarrierFullMenu JointCapacityRow

/-- The scalar menu discharges all numerical row and pair obligations.
The inputs only identify actual rows with envelopes and account for their
original physical scales; no count or weighted-sum bound is supplied. -/
def certifiedHistoryRows (w : List Factor) (T : ℝ)
    (labels : History w → Fin w.length → Label)
    (hlabels : ∀ h i, (rows h i).EffectivelyBoundedBy (envelope (labels h i)))
    (hscale : ∀ h, ∑ i, physicalScale (labels h i) = T) :
    CertifiedHistoryRows w T :=
  CertifiedHistoryRows.of_effectiveUpperRows w T
    (fun h i => envelope (labels h i)) hlabels
    (fun h i => BinaryCarrierFullMenuEnergy.color (labels h i))
    (fun h i => BinaryCarrierFullMenuEnergy.mass (labels h i))
    (fun h i => BinaryCarrierFullMenuEnergy.mass_nonneg (labels h i))
    (fun h i => BinaryCarrierFullMenuEnergy.head_le (labels h i))
    (fun h i => BinaryCarrierFullMenuEnergy.second_le (labels h i))
    (fun h a i _ => BinaryCarrierFullMenuEnergy.pair_le (labels h a) (labels h i))
    (by
      intro h
      change (∑ i, 4 * physicalScale (labels h i)) = 4 * T
      rw [← Finset.mul_sum, hscale h])

@[simp] theorem certifiedHistoryRows_mass (w : List Factor) (T : ℝ)
    (labels : History w → Fin w.length → Label)
    (hlabels : ∀ h i, (rows h i).EffectivelyBoundedBy (envelope (labels h i)))
    (hscale : ∀ h, ∑ i, physicalScale (labels h i) = T)
    (h : History w) (i : Fin w.length) :
    (certifiedHistoryRows w T labels hlabels hscale).mass h i =
      4 * physicalScale (labels h i) := rfl

/-- Every original history keeps its individual weight. Reusing a scalar
label at different positions or for different normals never merges them. -/
theorem normalHistorySum_le_reserve (w : List Factor) (T : ℝ)
    (labels : History w → Fin w.length → Label)
    (hlabels : ∀ h i, (rows h i).EffectivelyBoundedBy (envelope (labels h i)))
    (hscale : ∀ h, ∑ i, physicalScale (labels h i) = T)
    (v : AxisWeights w) (hv : WeightsNonnegative w v)
    (R j ell : ℝ) (hj : 0 ≤ j ∧ j ≤ R) (hell : 0 ≤ ell ∧ ell ≤ R / 2) :
    (2 : ℝ) ^ (ell * (R / 2 - ell) + (j - ell) * (R - j)) *
        normalHistorySum w v (j - ell) 0 ell ≤
      axisWeightProduct w v *
        (2 : ℝ) ^ ((R + 4 * T) ^ 2 / 4 - (25 / 82) * R * T - (29 / 164) * T ^ 2) :=
  BinaryCarrierWord.normalHistorySum_le_reserve w v hv T
    (certifiedHistoryRows w T labels hlabels hscale) R j ell hj hell

/-- The whole original marked subgroup family inherits the reserve with
the checked order loss and original axis-weight product still explicit. -/
theorem markedSum_le_reserve (w : List Factor) (T : ℝ)
    (labels : History w → Fin w.length → Label)
    (hlabels : ∀ h i, (rows h i).EffectivelyBoundedBy (envelope (labels h i)))
    (hscale : ∀ h, ∑ i, physicalScale (labels h i) = T)
    (b : ℕ) (hb : OrderBound w b)
    (v : AxisWeights w) (hv : WeightsNonnegative w v)
    (P : Subgroup (Product w) → Prop)
    (R j ell : ℝ) (hj : 0 ≤ j ∧ j ≤ R) (hell : 0 ≤ ell ∧ ell ≤ R / 2) :
    (2 : ℝ) ^ (ell * (R / 2 - ell) + (j - ell) * (R - j)) *
        markedSum w v P (j - ell) 0 ell ≤
      (((binaryStructuredOrderConstant b *
        (b * w.length + 2) ^ (binaryStructuredOrderConstant b) : ℕ) : ℝ) ^ w.length) *
        axisWeightProduct w v *
          (2 : ℝ) ^ ((R + 4 * T) ^ 2 / 4 - (25 / 82) * R * T - (29 / 164) * T ^ 2) :=
  BinaryCarrierWord.markedSum_le_reserve_of_orderBound w b hb v hv P T
    (certifiedHistoryRows w T labels hlabels hscale) R j ell hj hell

end SymmetricSubgroupAsymptotics.BinaryCarrierFullMenuHistory
