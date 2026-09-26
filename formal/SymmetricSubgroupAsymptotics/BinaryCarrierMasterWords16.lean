import SymmetricSubgroupAsymptotics.BinaryCarrierMasterMenuHistory
import SymmetricSubgroupAsymptotics.BinaryCarrierMasterEnvelopeCoverage16

/-! Arbitrary ordered words, with repetitions, in the five literal
degree-sixteen masters. Every original normal history receives the proved
numerical reserve. Original subgroup weights and arbitrary survival tests
remain explicit; no owner coverage or physical weight bound is inferred. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierMasterWords16

open BinaryCarrierWord BinaryCarrierMasterMenuHistory

inductive Master
  | t1082 | t1083 | t1084 | t1332 | t1547
  deriving DecidableEq, Fintype

/-- Each constructor names the literal original permutation closure. -/
def factor : Master → Factor
  | .t1082 => BinaryCarrierMasterEnvelopeCoverage16T1082.factor
  | .t1083 => BinaryCarrierMasterEnvelopeCoverage16T1083.factor
  | .t1084 => BinaryCarrierMasterEnvelopeCoverage16T1084.factor
  | .t1332 => BinaryCarrierMasterEnvelopeCoverage16T1332.factor
  | .t1547 => BinaryCarrierMasterEnvelopeCoverage16T1547.factor

/-- List.map preserves every position and every repeated original factor. -/
def word (masters : List Master) : List Factor := masters.map factor

@[simp] theorem word_length (masters : List Master) : (word masters).length = masters.length :=
  by simp only [word, List.length_map]

theorem covered_factor (m : Master) : CoveredFactor (factor m) := by
  cases m with
  | t1082 => exact BinaryCarrierMasterEnvelopeCoverage16T1082.actualRow_effectivelyBoundedBy_envelope
  | t1083 => exact BinaryCarrierMasterEnvelopeCoverage16T1083.actualRow_effectivelyBoundedBy_envelope
  | t1084 => exact BinaryCarrierMasterEnvelopeCoverage16T1084.actualRow_effectivelyBoundedBy_envelope
  | t1332 => exact BinaryCarrierMasterEnvelopeCoverage16T1332.actualRow_effectivelyBoundedBy_envelope
  | t1547 => exact BinaryCarrierMasterEnvelopeCoverage16T1547.actualRow_effectivelyBoundedBy_envelope

theorem covered_word (masters : List Master) : CoveredWord (word masters) := by
  intro A hA
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp hA
  exact covered_factor m

theorem factor_card_le (m : Master) : Nat.card (factor m).Carrier ≤ 2 ^ 12 := by
  cases m with
  | t1082 =>
      change Nat.card BinaryCarrierExactOrder16T1082.Original ≤ 2 ^ 12
      rw [BinaryCarrierExactOrder16T1082.original_card]
      decide
  | t1083 =>
      change Nat.card BinaryCarrierExactOrder16T1083.Original ≤ 2 ^ 12
      rw [BinaryCarrierExactOrder16T1083.original_card]
      decide
  | t1084 =>
      change Nat.card BinaryCarrierExactOrder16T1084.Original ≤ 2 ^ 12
      rw [BinaryCarrierExactOrder16T1084.original_card]
      decide
  | t1332 =>
      change Nat.card BinaryCarrierExactOrder16T1332.Original ≤ 2 ^ 12
      rw [BinaryCarrierExactOrder16T1332.original_card]
      decide
  | t1547 =>
      change Nat.card BinaryCarrierExactOrder16T1547.Original ≤ 2 ^ 12
      exact BinaryCarrierExactOrder16T1547.original_card.le

theorem orderBound (masters : List Master) : OrderBound (word masters) 12 := by
  induction masters with
  | nil => exact True.intro
  | cons m masters ih => exact ⟨factor_card_le m, ih⟩

/-- Mass eight is attached to EACH original position, even when factors
or envelope labels repeat. The total physical scale is twice the length. -/
def certifiedHistoryRows (masters : List Master) :
    CertifiedHistoryRows (word masters) (2 * (masters.length : ℝ)) := by
  simpa only [totalScale, word_length] using
    BinaryCarrierMasterMenuHistory.certifiedHistoryRows (word masters) (covered_word masters)

theorem normalHistorySum_le_reserve (masters : List Master)
    (v : AxisWeights (word masters)) (hv : WeightsNonnegative (word masters) v)
    (R j ell : ℝ) (hj : 0 ≤ j ∧ j ≤ R) (hell : 0 ≤ ell ∧ ell ≤ R/2) :
    (2 : ℝ)^(ell*(R/2-ell)+(j-ell)*(R-j)) *
        normalHistorySum (word masters) v (j-ell) 0 ell ≤
      axisWeightProduct (word masters) v *
        (2 : ℝ)^((R+4*(2*(masters.length : ℝ)))^2/4 -
          (25/82)*R*(2*(masters.length : ℝ)) - (29/164)*(2*(masters.length : ℝ))^2) :=
  BinaryCarrierWord.normalHistorySum_le_reserve (word masters) v hv
    (2*(masters.length : ℝ)) (certifiedHistoryRows masters) R j ell hj hell

/-- The complete original marked sum, with the original weight product
and uniform polynomial factor still visible. No bound on these weights
or implication for a global ordinary remainder is assumed. -/
theorem markedSum_le_reserve (masters : List Master)
    (v : AxisWeights (word masters)) (hv : WeightsNonnegative (word masters) v)
    (P : Subgroup (Product (word masters)) → Prop)
    (R j ell : ℝ) (hj : 0 ≤ j ∧ j ≤ R) (hell : 0 ≤ ell ∧ ell ≤ R/2) :
    (2 : ℝ)^(ell*(R/2-ell)+(j-ell)*(R-j)) *
        markedSum (word masters) v P (j-ell) 0 ell ≤
      (((binaryStructuredOrderConstant 12 *
        (12*masters.length+2)^(binaryStructuredOrderConstant 12) : ℕ) : ℝ)^masters.length) *
        axisWeightProduct (word masters) v *
          (2 : ℝ)^((R+4*(2*(masters.length : ℝ)))^2/4 -
            (25/82)*R*(2*(masters.length : ℝ)) - (29/164)*(2*(masters.length : ℝ))^2) := by
  simpa only [word_length] using
    BinaryCarrierWord.markedSum_le_reserve_of_orderBound
      (word masters) 12 (orderBound masters) v hv P
      (2*(masters.length : ℝ)) (certifiedHistoryRows masters) R j ell hj hell

end SymmetricSubgroupAsymptotics.BinaryCarrierMasterWords16
