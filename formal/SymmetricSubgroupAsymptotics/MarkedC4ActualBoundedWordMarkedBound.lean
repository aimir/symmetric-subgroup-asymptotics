import SymmetricSubgroupAsymptotics.MarkedC4ActualOriginalWordHistoryEndpoint

/-! The actual marked bounded-word endpoint, with the single Hall factor
and a proved negligible physical error. No decomposition input is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualBoundedWordMarkedBound
open RDTOriginalWordStructure RDTNormalFInterface

theorem marked_bound
    (hKP : KovacsPraegerBinaryAbelianQuotientBound) (h55 : PublishedTheorem55Binary)
    (h53 : ActualCaseIITargetStructure.PublishedProposition53Binary)
    (h57 : RDTExcessStructure.PublishedTheorem57Binary)
    (h8 : RDTDegreeEightExceptional.PublishedDegreeEightExceptional)
    (hderived : RDTDerivedNormalQuarter.PublishedDerivedNormalQuarterBinary)
    (lit : RDTTheorem46BinaryInput)
    {t : ℕ} (n : Fin t → ℕ) (G : ∀ i,Subgroup (Equiv.Perm (Fin (n i))))
    (C b r : ℕ) (hb : 1 ≤ b) (hsum : (∑ i : Fin t,n i)=b)
    (hpositive : ∀ i,0<n i) (hcut : ∀ i,n i≤C)
    (hG : ∀ i,IsPGroup 2 (G i))
    (htrans : ∀ i,∀ x y : Fin (n i),∃ g : G i,g.val x=y) :
    (Nat.card (ActualFullPhysicalWordPeel.Family (fun i => ↥(G i))
      (ActualGlobalMarkGeneratorRank.Marks r)) : ℝ) ≤
      VerticalHallBase.polynomial r *
        (2 : ℝ)^(markedF b r+boundedWordError (HistoryMenuError.coefficient lit C) b r) := by
  have hB : (∑ i : Fin t,n i)≤b := hsum.le
  have ht := ActualOriginalWordHistoryEndpoint.physical_length_le n b hpositive hB
  have hh := ActualOriginalWordHistoryEndpoint.marked_word_le hKP h55 h53 h57 h8 hderived lit
    n G C b r hpositive hcut hG htrans hB
  have hr : (∑ i : Fin t,(n i : ℝ))=(b : ℝ) := by exact_mod_cast hsum
  rw [hr] at hh
  have hp : 0 ≤ VerticalHallBase.polynomial r :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (VerticalHallBase.polynomial_one_le r)
  have he := HistoryMenuError.cost_le_error lit C b r t hb ht
  apply hh.trans
  calc
    _ ≤ (VerticalHallBase.polynomial r *
        (2 : ℝ)^boundedWordError (HistoryMenuError.coefficient lit C) b r)*
        (2 : ℝ)^markedF b r :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hp) (by positivity)
    _ = _ := by
      rw [mul_assoc,← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
      congr 2
      ring

end SymmetricSubgroupAsymptotics.MarkedC4.ActualBoundedWordMarkedBound
