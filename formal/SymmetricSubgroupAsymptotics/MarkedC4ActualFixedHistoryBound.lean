import SymmetricSubgroupAsymptotics.MarkedC4ActualChosenHistoryCaseI
import SymmetricSubgroupAsymptotics.MarkedC4ActualChosenHistoryPositive
import SymmetricSubgroupAsymptotics.MarkedC4ActualFullPhysicalWordZero

/-! Fixed-history induction with an INITIAL physical budget B. Each
positive step pays only the uniform epi polynomial; the terminal Case-I
cost and the vertical P(r) are paid ONCE. No recurrence/count is input. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualFixedHistoryBound
open ActualChosenHistorySchedule ActualHistoryPriority RDTOriginalWordStructure RDTNormalFInterface

 def stoppingCost (C B : ℕ) : ℝ :=
  ((B : ℝ)+2)^ActualUniformOriginalCaseI.costExponent C B

def envelope (lit : RDTTheorem46BinaryInput) (C B r t : ℕ) : ℝ :=
  VerticalHallBase.polynomial r*stoppingCost C B*(ActualUniformEpiReserve.peelFactor lit C B r)^t

theorem stoppingCost_one_le (C B : ℕ) : 1 ≤ stoppingCost C B := by
  apply Real.one_le_rpow
  · have : (0 : ℝ)≤B := Nat.cast_nonneg _
    linarith
  · unfold ActualUniformOriginalCaseI.costExponent
    positivity

theorem peelFactor_one_le (lit : RDTTheorem46BinaryInput) (C B r : ℕ) :
    1≤ActualUniformEpiReserve.peelFactor lit C B r := by
  unfold ActualUniformEpiReserve.peelFactor
  have hp : (1 : ℝ) ≤ ((B : ℝ)+(r : ℝ)+2)^ActualNormalFMarkedPeel.kappa4 lit (2+C) := by
    apply Real.one_le_rpow
    · have hB : (0 : ℝ)≤B := Nat.cast_nonneg _
      have hr : (0 : ℝ)≤r := Nat.cast_nonneg _
      linarith
    · exact ActualNormalFMarkedPeel.kappa4_nonneg lit (2+C)
  simpa only [one_mul] using mul_le_mul (le_max_right (ActualNormalFMarkedPeel.kappa3 lit (2+C)) 1) hp
    (by norm_num : (0 : ℝ) ≤ 1) (le_trans (by norm_num) (le_max_right _ _))

/-- Final bound for every chosen fixed ORIGINAL history. The hypotheses
are ordinary literature plus the actual physical actions and structural
finite chosen-order condition; no numerical recurrence is supplied. -/
theorem card_le
    (hKP : KovacsPraegerBinaryAbelianQuotientBound) (h55 : PublishedTheorem55Binary)
    (h53 : ActualCaseIITargetStructure.PublishedProposition53Binary)
    (h57 : RDTExcessStructure.PublishedTheorem57Binary)
    (h8 : RDTDegreeEightExceptional.PublishedDegreeEightExceptional)
    (hderived : RDTDerivedNormalQuarter.PublishedDerivedNormalQuarterBinary)
    (lit : RDTTheorem46BinaryInput) (C B r : ℕ) :
    ∀ (t : ℕ) (n : Fin t → ℕ) (G : ∀ i,Subgroup (Equiv.Perm (Fin (n i))))
      (D : Data n G),Chosen D →(∀ i,0<n i) →(∀ i,n i≤C) →
      (∀ i,IsPGroup 2 (G i)) →
      (∀ i,∀ x y : Fin (n i),∃ g : G i,g.val x=y) →
      (∑ i : Fin t,n i)≤B →
      (Nat.card (Family D (ActualGlobalMarkGeneratorRank.Marks r)) : ℝ)≤
        envelope lit C B r t*(2 : ℝ)^markedF (∑ i : Fin t,(n i : ℝ)) r := by
  intro t
  induction t with
  | zero =>
    intro n G D hD hpositive hcut hG htrans hB
    have hi : (Nat.card (Family D (ActualGlobalMarkGeneratorRank.Marks r)) : ℝ)≤
        Nat.card (ActualFullPhysicalWordPeel.Family (fun i => ↥(G i)) (ActualGlobalMarkGeneratorRank.Marks r)) := by
      exact_mod_cast Nat.card_le_card_of_injective
        (fun J : Family D (ActualGlobalMarkGeneratorRank.Marks r) => J.val) Subtype.val_injective
    have hz := hi.trans (ActualFullPhysicalWordZero.zero_marked_le (fun i => ↥(G i)) r)
    have hp0 : 0≤VerticalHallBase.polynomial r :=
      (show (0 : ℝ)≤1 by norm_num).trans (VerticalHallBase.polynomial_one_le r)
    have he := le_mul_of_one_le_right hp0 (stoppingCost_one_le C B)
    have hh := hz.trans (mul_le_mul_of_nonneg_right he (by positivity))
    simpa [envelope] using hh
  | succ t ih =>
    intro n G D hD hpositive hcut hG htrans hB
    by_cases hz : normalPriority (n 0) (G 0) ⟨(D.rows 0).val 0,D.normal 0 0⟩=0
    · have hs := ActualChosenHistoryCaseI.card_le n G D hKP h53 C hpositive hcut hG htrans hD hz B r hB
      have hp0 : 0≤VerticalHallBase.polynomial r :=
        (show (0 : ℝ)≤1 by norm_num).trans (VerticalHallBase.polynomial_one_le r)
      have ht0 : 0 ≤ stoppingCost C B := (show (0 : ℝ)≤1 by norm_num).trans (stoppingCost_one_le C B)
      have he := le_mul_of_one_le_right (mul_nonneg hp0 ht0)
        (one_le_pow₀ (peelFactor_one_le lit C B r) : 1≤(ActualUniformEpiReserve.peelFactor lit C B r)^(t+1))
      exact hs.trans (mul_le_mul_of_nonneg_right he (by positivity))
    · have hp : 0<normalPriority (n 0) (G 0) ⟨(D.rows 0).val 0,D.normal 0 0⟩ := Nat.pos_of_ne_zero hz
      have hs := ActualChosenHistoryPositive.card_le_suffix n G D hKP h55 h53 h57 h8 hderived lit
        C hcut hG htrans hD hp B r hB
      have hBtail : (∑ j : Fin t,n j.succ)≤B := by
        have hh := Fin.sum_univ_succ n
        omega
      have hi := ih (fun j : Fin t => n j.succ) (fun j => G j.succ) (suffix D)
        (chosen_suffix D hD) (fun j => hpositive j.succ) (fun j => hcut j.succ)
        (fun j => hG j.succ) (fun j => htrans j.succ) hBtail
      have hmul := mul_le_mul_of_nonneg_left hi
        (show 0≤ActualUniformEpiReserve.peelFactor lit C B r*
          (2 : ℝ)^(markedF (∑ i : Fin (t+1),(n i : ℝ)) r-
            markedF (∑ j : Fin t,(n j.succ : ℝ)) r) from
          mul_nonneg ((show (0 : ℝ)≤1 by norm_num).trans (peelFactor_one_le lit C B r)) (by positivity))
      apply hs.trans (hmul.trans_eq ?_)
      have htel : (2 : ℝ)^(markedF (∑ i : Fin (t+1),(n i : ℝ)) r-
          markedF (∑ j : Fin t,(n j.succ : ℝ)) r)*
          (2 : ℝ)^markedF (∑ j : Fin t,(n j.succ : ℝ)) r=
          (2 : ℝ)^markedF (∑ i : Fin (t+1),(n i : ℝ)) r := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
        congr 1
        ring
      unfold envelope
      calc
        _=VerticalHallBase.polynomial r*stoppingCost C B*
          ((ActualUniformEpiReserve.peelFactor lit C B r)^t*ActualUniformEpiReserve.peelFactor lit C B r)*
          ((2 : ℝ)^(markedF (∑ i : Fin (t+1),(n i : ℝ)) r-
            markedF (∑ j : Fin t,(n j.succ : ℝ)) r)*
              (2 : ℝ)^markedF (∑ j : Fin t,(n j.succ : ℝ)) r) := by ring
        _=_ := by rw [← pow_succ,htel]

end SymmetricSubgroupAsymptotics.MarkedC4.ActualFixedHistoryBound
