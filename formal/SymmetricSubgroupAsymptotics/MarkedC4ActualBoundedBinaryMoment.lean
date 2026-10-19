import SymmetricSubgroupAsymptotics.MarkedC4ActualBinarySkeletonMenu
import SymmetricSubgroupAsymptotics.MarkedC4ActualBoundedWordMarkedBound
import SymmetricSubgroupAsymptotics.MarkedC4BoundedNilpotentTargetConvolution

/-! The literal bounded binary moment is bounded through actual original
words, graph fibres, and one global skeleton/history menu. All hypotheses
below are named ordinary unmarked literature, not project count inputs. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualBoundedBinaryMoment
open RDTOriginalWordStructure RDTNormalFInterface ActualBinaryWordSkeletons

def physicalMenu (C b : ℕ) : ℝ :=
  (b.factorial*(b+1)*(max C 1)^b*(ActualBinarySkeletonMenu.letterBound C)^b : ℕ)

theorem marked_bound
    (hKP : KovacsPraegerBinaryAbelianQuotientBound) (h55 : PublishedTheorem55Binary)
    (h53 : ActualCaseIITargetStructure.PublishedProposition53Binary)
    (h57 : RDTExcessStructure.PublishedTheorem57Binary)
    (h8 : RDTDegreeEightExceptional.PublishedDegreeEightExceptional)
    (hderived : RDTDerivedNormalQuarter.PublishedDerivedNormalQuarterBinary)
    (lit : RDTTheorem46BinaryInput) (C b r : ℕ) (hb : 1 ≤ b) :
    BoundedNilpotentTargetConvolution.binaryMoment C b r ≤
      physicalMenu C b * VerticalHallBase.polynomial r *
        (2 : ℝ)^(markedF b r+boundedWordError (HistoryMenuError.coefficient lit C) b r) := by
  let R : ℝ := VerticalHallBase.polynomial r *
    (2 : ℝ)^(markedF b r+boundedWordError (HistoryMenuError.coefficient lit C) b r)
  have hR : 0 ≤ R := by
    have hp : 0 ≤ VerticalHallBase.polynomial r :=
      (by norm_num : (0 : ℝ) ≤ 1).trans (VerticalHallBase.polynomial_one_le r)
    exact mul_nonneg hp (by positivity)
  have hf : ∀ p : Skeleton C b,
      (Nat.card (ActualFullPhysicalWordPeel.Family (Factors p)
        (ActualGlobalMarkGeneratorRank.Marks r)) : ℝ) ≤ R := by
    intro p
    exact ActualBoundedWordMarkedBound.marked_bound hKP h55 h53 h57 h8 hderived lit
      (fun i => (p.val.1.degrees i).val) p.val.2 C b r hb p.val.1.total
      p.val.1.positive (fun i => (p.val.1.degrees i).isLt.le) p.property.1 p.property.2
  have hw : BinaryWordFamilyEncoding.wordCount C b r ≤ (Nat.card (Skeleton C b) : ℝ)*R := by
    apply (wordCount_le C b r).trans
    calc
      _ ≤ ∑ _p : Skeleton C b,R := Finset.sum_le_sum (fun p _ => hf p)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
  have hk : (Nat.card (Skeleton C b) : ℝ) ≤
      ((b+1)*(max C 1)^b*(ActualBinarySkeletonMenu.letterBound C)^b : ℕ) := by
    exact_mod_cast ActualBinarySkeletonMenu.skeleton_card_le C b
  have hh := (BinaryWordFamilyEncoding.moment_le C b r).trans
    (mul_le_mul_of_nonneg_left (hw.trans (mul_le_mul_of_nonneg_right hk hR))
      (Nat.cast_nonneg b.factorial))
  change BoundedNilpotentTargetConvolution.binaryMoment C b r ≤ _ at hh
  dsimp only [R] at hh
  convert hh using 1 <;> simp only [physicalMenu,Nat.cast_mul] <;> ring

end SymmetricSubgroupAsymptotics.MarkedC4.ActualBoundedBinaryMoment
