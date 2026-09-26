import SymmetricSubgroupAsymptotics.PrimeEvaluationKernelOrder
import SymmetricSubgroupAsymptotics.BinaryCarrierMasterRankBounds16
import SymmetricSubgroupAsymptotics.BinaryCarrierWordHistory
import SymmetricSubgroupAsymptotics.JointCapacityRowEnvelope

/-! One actual row at the derived axis of the literal 16T1082 closure.
The original group is proved to be a 2-group from its evaluation kernel
and its certified derived order. Its six original generators give the
ambient order budget and the abelian quotient slope. This installs only
the displayed original axis, not an all-normal row or owner cover. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierDerivedAxis16T1082

open FullSubdirectGoursat BinaryMarkedGoursatPeel

abbrev Original := BinaryCarrierRank16T1082.Original

theorem original_isPGroup : IsPGroup 2 Original :=
  isPGroup_of_evaluationKernel_eq 2
    BinaryCarrierDerived16T1082.evaluationKernel_eq_commutator 4
    (by simpa only [show (2 : ℕ)^4 = 16 from by decide] using
      BinaryCarrierDerivedOrder16T1082.card_commutator)

theorem original_card_le : Nat.card Original ≤ 2^10 := by
  simpa only [Fintype.card_fin] using
    card_le_prime_pow_of_evaluationKernel_eq 2
      (closureGenerators BinaryActionData16.node1082Generators)
      (closureGenerators_full BinaryActionData16.node1082Generators)
      BinaryCarrierDerived16T1082.evaluationKernel_eq_commutator 4
      (by simpa only [show (2 : ℕ)^4 = 16 from by decide] using
        BinaryCarrierDerivedOrder16T1082.card_commutator)

theorem quotient_card_le : Nat.card (Original ⧸ commutator Original) ≤ 2^6 := by
  simpa only [Fintype.card_fin] using
    card_quotient_commutator_le_of_evaluationKernel_eq 2
      (closureGenerators BinaryActionData16.node1082Generators)
      (closureGenerators_full BinaryActionData16.node1082Generators)
      BinaryCarrierDerived16T1082.evaluationKernel_eq_commutator

/-- The carrier is the literal original permutation closure. -/
def factor : BinaryCarrierWord.Factor where
  Carrier := Original
  group := inferInstance
  finite := inferInstance
  binary := original_isPGroup

/-- The selected axis is the actual original derived subgroup. -/
def derivedAxis : NormalAxis Original := ⟨commutator Original, inferInstance⟩

theorem head_le : head derivedAxis ≤ 3 :=
  (primeRelativeHead_le_normalHeadMax 2 (commutator Original)
    (commutator Original) le_rfl).trans BinaryCarrierRank16T1082.derivedNormalRank_le

theorem orderLog_eq : orderLog derivedAxis = 4 := by
  change Nat.log 2 (Nat.card (commutator Original)) = 4
  rw [BinaryCarrierDerivedOrder16T1082.card_commutator]
  decide

theorem max_heads_le : max (derivedHead derivedAxis) (radicalHead derivedAxis) ≤ 3 :=
  BinaryCarrierRank16T1082.max_heads_le derivedAxis

theorem centerSlope_le : centerSlope derivedAxis ≤ 6 := by
  rw [centerSlope_eq_log_quotient_of_commutator_le derivedAxis le_rfl]
  have h := Nat.log_monotone (b := 2) quotient_card_le
  rw [Nat.log_pow (by decide : 1 < (2 : ℕ))] at h
  exact h

theorem derivedSlope_eq : derivedSlope derivedAxis = 0 :=
  derivedSlope_eq_zero_of_commutator_le derivedAxis le_rfl

/-- A numerical upper row for this one literal axis. Its order coordinate
is deliberately relaxed from the certified 4 to 6. -/
def upperRow : JointCapacityRow where
  k := 3
  n := 6
  m := 3
  a₂ := 3
  c := 6
  g := 0

/-- All six inequalities concern the same original normal axis. -/
theorem actualRow_bounded :
    JointCapacityRow.BoundedBy
      (BinaryCarrierWord.actualRow (A := factor) derivedAxis) upperRow := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact head_le
  · change orderLog derivedAxis ≤ 6
    rw [orderLog_eq]
    decide
  · exact (le_max_left _ _).trans max_heads_le
  · exact (le_max_right _ _).trans max_heads_le
  · change (centerSlope derivedAxis : ℝ) ≤ 6
    exact_mod_cast centerSlope_le
  · change (derivedSlope derivedAxis : ℝ) ≤ 0
    rw [derivedSlope_eq]
    norm_num

end SymmetricSubgroupAsymptotics.BinaryCarrierDerivedAxis16T1082
