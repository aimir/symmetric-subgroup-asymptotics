import SymmetricSubgroupAsymptotics.MarkedC4ActualBoundedBinaryMoment
import SymmetricSubgroupAsymptotics.MarkedC4ActualBinaryZero
import SymmetricSubgroupAsymptotics.MarkedC4SkeletonMenuError
import SymmetricSubgroupAsymptotics.MarkedC4SingleMarkError

/-! A proved all-physical-degree monotone negligible error for the actual
bounded binary moment. This is ready for the physical odd convolution. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualBoundedBinaryError
open RDTOriginalWordStructure RDTNormalFInterface

def error (lit : RDTTheorem46BinaryInput) (C b r : ℕ) : ℝ :=
  SingleMarkError.error b r + boundedWordError (SkeletonMenuError.coefficient C) b r +
    boundedWordError (HistoryMenuError.coefficient lit C) b r

theorem negligible (lit : RDTTheorem46BinaryInput) (C : ℕ) :
    UniformQuadraticNegligible (error lit C) :=
  (SingleMarkError.negligible.add (SkeletonMenuError.negligible C)).add
    (HistoryMenuError.negligible lit C)

private theorem wordError_mono {A : ℝ} (hA : 0 ≤ A) {a b : ℕ} (hab : a≤b) (r : ℕ) :
    boundedWordError A a r ≤ boundedWordError A b r := by
  have hc : 0 ≤ (A+1)/Real.log 2 := div_nonneg (by linarith) (Real.log_pos (by norm_num)).le
  have habR : (a : ℝ)≤b := by exact_mod_cast hab
  have hl0 : 0 ≤ Real.log ((a : ℝ)+r+2) := Real.log_nonneg (by
    linarith [Nat.cast_nonneg (α := ℝ) a,Nat.cast_nonneg (α := ℝ) r])
  have hl : Real.log ((a : ℝ)+r+2) ≤ Real.log ((b : ℝ)+r+2) :=
    Real.log_le_log (by positivity) (by linarith)
  exact mul_le_mul (mul_le_mul_of_nonneg_left habR hc) hl hl0
    (mul_nonneg hc (Nat.cast_nonneg b))

theorem mono (lit : RDTTheorem46BinaryInput) (C a b r : ℕ) (hab : a≤b) :
    error lit C a r≤error lit C b r := by
  unfold error SingleMarkError.error
  exact add_le_add (add_le_add le_rfl
    (wordError_mono (SkeletonMenuError.coefficient_nonneg C) hab r))
    (wordError_mono (HistoryMenuError.coefficient_nonneg lit C) hab r)

theorem marked_bound
    (hKP : KovacsPraegerBinaryAbelianQuotientBound) (h55 : PublishedTheorem55Binary)
    (h53 : ActualCaseIITargetStructure.PublishedProposition53Binary)
    (h57 : RDTExcessStructure.PublishedTheorem57Binary)
    (h8 : RDTDegreeEightExceptional.PublishedDegreeEightExceptional)
    (hderived : RDTDerivedNormalQuarter.PublishedDerivedNormalQuarterBinary)
    (lit : RDTTheorem46BinaryInput) (C b r : ℕ) :
    BoundedNilpotentTargetConvolution.binaryMoment C b r ≤
      (2 : ℝ)^(markedF b r+error lit C b r) := by
  by_cases hb : b=0
  · subst b
    apply (ActualBinaryZero.moment_le_one C r).trans
    apply Real.one_le_rpow (by norm_num : (1 : ℝ)≤2)
    have hp := Real.logb_nonneg (by norm_num : (1 : ℝ)<2)
      (VerticalHallBase.polynomial_one_le r)
    have hs := boundedWordError_nonneg (SkeletonMenuError.coefficient_nonneg C) 0 r
    have hh := boundedWordError_nonneg (HistoryMenuError.coefficient_nonneg lit C) 0 r
    unfold error SingleMarkError.error markedF
    push_cast
    nlinarith [sq_nonneg (r : ℝ)]
  · have hb1 : 1≤b := by omega
    have hh := ActualBoundedBinaryMoment.marked_bound hKP h55 h53 h57 h8 hderived lit C b r hb1
    have hm : ActualBoundedBinaryMoment.physicalMenu C b=SkeletonMenuError.cost C b := by
      simp only [ActualBoundedBinaryMoment.physicalMenu,SkeletonMenuError.cost,
        ActualBinarySkeletonMenu.letterBound,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one,
        Nat.cast_ofNat]
    rw [hm] at hh
    have hp : 0 ≤ VerticalHallBase.polynomial r :=
      (by norm_num : (0 : ℝ) ≤ 1).trans (VerticalHallBase.polynomial_one_le r)
    have he := SkeletonMenuError.cost_le_error C b r hb1
    apply hh.trans
    calc
      _ ≤ (2 : ℝ)^boundedWordError (SkeletonMenuError.coefficient C) b r *
          VerticalHallBase.polynomial r *
          (2 : ℝ)^(markedF b r+boundedWordError (HistoryMenuError.coefficient lit C) b r) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he hp) (by positivity)
      _ = _ := by
        rw [SingleMarkError.polynomial_eq_exp b r,
          ← Real.rpow_add (by norm_num : (0 : ℝ)<2),
          ← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
        congr 1
        unfold error
        ring

end SymmetricSubgroupAsymptotics.MarkedC4.ActualBoundedBinaryError
