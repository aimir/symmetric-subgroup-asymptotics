import SymmetricSubgroupAsymptotics.MarkedC4ActualGlobalHistoryBound
import SymmetricSubgroupAsymptotics.MarkedC4ActualBinaryPhysicalOrderBudget
import SymmetricSubgroupAsymptotics.MarkedC4HistoryMenuError

/-! Actual original bounded binary words: all keys and all excessive
histories are counted, with no numerical or structural reduction input.
Only the named ordinary unmarked literature remains as hypotheses. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualOriginalWordHistoryEndpoint
open RDTOriginalWordStructure RDTNormalFInterface

theorem marked_word_le
    (hKP : KovacsPraegerBinaryAbelianQuotientBound) (h55 : PublishedTheorem55Binary)
    (h53 : ActualCaseIITargetStructure.PublishedProposition53Binary)
    (h57 : RDTExcessStructure.PublishedTheorem57Binary)
    (h8 : RDTDegreeEightExceptional.PublishedDegreeEightExceptional)
    (hderived : RDTDerivedNormalQuarter.PublishedDerivedNormalQuarterBinary)
    (lit : RDTTheorem46BinaryInput)
    {t : ℕ} (n : Fin t → ℕ) (G : ∀ i,Subgroup (Equiv.Perm (Fin (n i))))
    (C B r : ℕ) (hpositive : ∀ i,0<n i) (hcut : ∀ i,n i≤C)
    (hG : ∀ i,IsPGroup 2 (G i))
    (htrans : ∀ i,∀ x y : Fin (n i),∃ g : G i,g.val x=y)
    (hB : (∑ i : Fin t,n i)≤B) :
    (Nat.card (ActualFullPhysicalWordPeel.Family (fun i => ↥(G i))
      (ActualGlobalMarkGeneratorRank.Marks r)) : ℝ) ≤
      VerticalHallBase.polynomial r * HistoryMenuError.cost lit C B r t *
        (2 : ℝ)^markedF (∑ i : Fin t,(n i : ℝ)) r := by
  have hk : ∀ i,Nat.card (G i)≤2^C := by
    intro i
    exact (ActualBinaryPhysicalOrderBudget.original_card_le (n i) (G i) (hG i)).trans
      (pow_le_pow_right₀ (by norm_num : 1≤(2 : ℕ)) (hcut i))
  have hh := ActualGlobalHistoryBound.card_le hKP h55 h53 h57 h8 hderived lit
    n G C B r (2^C) hk hpositive hcut hG htrans hB
  have hm : ActualGlobalHistoryBound.menuCost t (2^C)=HistoryMenuError.menuCost C t := by
    simp only [ActualGlobalHistoryBound.menuCost,HistoryMenuError.menuCost,
      Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one]
  rw [hm] at hh
  unfold ActualFixedHistoryBound.envelope ActualFixedHistoryBound.stoppingCost at hh
  unfold HistoryMenuError.cost
  convert hh using 1 <;> ring

theorem physical_length_le {t : ℕ} (n : Fin t → ℕ) (B : ℕ)
    (hpositive : ∀ i,0<n i) (hB : (∑ i : Fin t,n i)≤B) : t≤B := by
  have hh : (∑ i : Fin t,1)≤∑ i : Fin t,n i :=
    Finset.sum_le_sum (fun i _ => hpositive i)
  simpa using hh.trans hB

end SymmetricSubgroupAsymptotics.MarkedC4.ActualOriginalWordHistoryEndpoint
