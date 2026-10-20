import SymmetricSubgroupAsymptotics.MarkedC4ActualChosenHistorySchedule
import SymmetricSubgroupAsymptotics.MarkedC4ActualNormalPriorityTarget
import SymmetricSubgroupAsymptotics.MarkedC4ActualUniformOriginalCaseI

/-! Actual terminal bound for a chosen fixed original history. Normalizing
its prescribed current menu is injective, canonical zero priorities give
Case I, and ONE global P(r) is paid at this stopping leaf only. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualChosenHistoryCaseI
open ActualChosenHistorySchedule ActualHistoryPriority ActualAbelianFactorSplit

 theorem caseI_cost_mono (C b B : ℕ) (hb : b≤B) :
    ((b : ℝ)+2)^ActualUniformOriginalCaseI.costExponent C b≤
      ((B : ℝ)+2)^ActualUniformOriginalCaseI.costExponent C B := by
  have hbr : (b : ℝ)≤B := by exact_mod_cast hb
  have he0 : 0≤ActualUniformOriginalCaseI.costExponent C b := by
    unfold ActualUniformOriginalCaseI.costExponent
    positivity
  have he : ActualUniformOriginalCaseI.costExponent C b≤ActualUniformOriginalCaseI.costExponent C B := by
    unfold ActualUniformOriginalCaseI.costExponent
    apply add_le_add
    · exact_mod_cast Nat.add_le_add_right
        (Nat.add_le_add_right (Nat.mul_le_mul_left (1+2^(2^C)) hb) (3*C)) 2
    · exact mul_le_mul_of_nonneg_right hbr (sq_nonneg (C : ℝ))
  calc
    _≤((B : ℝ)+2)^ActualUniformOriginalCaseI.costExponent C b :=
      Real.rpow_le_rpow (by positivity) (by linarith) he0
    _≤_ := Real.rpow_le_rpow_of_exponent_le (by have := Nat.cast_nonneg (α := ℝ) B; linarith) he

variable {t : ℕ} (n : Fin (t+1) → ℕ)
  (G : ∀ i,Subgroup (Equiv.Perm (Fin (n i))))
  (D : Data n G)
local notation "N" => ActualHistorySchedule.currentMenu (fun i => (G i : Type)) D.rows (fun i => D.normal i 0)
local instance normalAt (i : Fin (t+1)) : (N i).val.Normal := (N i).property
abbrev Factors := fun i => G i ⧸ (N i).val

def normalizedCode (r : ℕ) (J : Family D (ActualGlobalMarkGeneratorRank.Marks r)) :
    ActualFullPhysicalWordPeel.Family (Factors n G D) (ActualGlobalMarkGeneratorRank.Marks r) :=
  (ActualFixedNormalWordPeel.normalize (fun i => ↥(G i))
    (ActualGlobalMarkGeneratorRank.Marks r) N
    (ActualHistorySchedule.fixedStage (fun i => ↥(G i)) (ActualGlobalMarkGeneratorRank.Marks r)
      D.rows (fun i => D.normal i 0) J)).val

theorem normalizedCode_injective (r : ℕ) : Function.Injective (normalizedCode n G D r) := by
  intro J K h
  apply ActualHistorySchedule.fixedStage_injective (fun i => ↥(G i))
    (ActualGlobalMarkGeneratorRank.Marks r) D.rows (fun i => D.normal i 0)
  apply ActualFixedNormalWordPeel.normalize_injective (fun i => ↥(G i))
    (ActualGlobalMarkGeneratorRank.Marks r) N
  exact Subtype.ext h

/-- Actual stopping leaf, uniformly bounded using the INITIAL physical
budget B. The quotient factors retain their original degree n_i. -/
theorem card_le (hKP : KovacsPraegerBinaryAbelianQuotientBound)
    (h53 : ActualCaseIITargetStructure.PublishedProposition53Binary)
    (C : ℕ) (hpositive : ∀ i,0<n i) (hcut : ∀ i,n i≤C)
    (hG : ∀ i,IsPGroup 2 (G i))
    (htrans : ∀ i,∀ x y : Fin (n i),∃ g : G i,g.val x=y)
    (hD : Chosen D)
    (hz : normalPriority (n 0) (G 0) ⟨(D.rows 0).val 0,D.normal 0 0⟩=0)
    (B r : ℕ) (hB : (∑ i : Fin (t+1),n i)≤B) :
    (Nat.card (Family D (ActualGlobalMarkGeneratorRank.Marks r)) : ℝ)≤
      VerticalHallBase.polynomial r*
        ((B : ℝ)+2)^ActualUniformOriginalCaseI.costExponent C B*
          (2 : ℝ)^markedF (∑ i : Fin (t+1),(n i : ℝ)) r := by
  have hquarter : ∀ i,¬Abelian (Factors n G D) i →
      ∀ V : Subgroup ((Factors n G D) i),V.Normal →(normalGen V : ℝ)≤(n i : ℝ)/4 := by
    intro i hab V hV
    have hi := hD 0 i (Nat.zero_le _)
    rw [hz] at hi
    have hzi := Nat.eq_zero_of_le_zero hi
    exact ActualNormalPriorityTarget.quarter_of_zero h53 (n i) (G i) (hG i) (htrans i)
      (N i) hzi hab V hV
  have hc := ActualUniformOriginalCaseI.marked_word_card_le hKP n C hpositive hcut G hG
    (Factors n G D) (fun i => QuotientGroup.mk' (N i).val)
    (fun i => QuotientGroup.mk'_surjective (N i).val) hquarter r
  have hinj : (Nat.card (Family D (ActualGlobalMarkGeneratorRank.Marks r)) : ℝ)≤
      Nat.card (ActualFullPhysicalWordPeel.Family (Factors n G D) (ActualGlobalMarkGeneratorRank.Marks r)) := by
    exact_mod_cast Nat.card_le_card_of_injective (normalizedCode n G D r) (normalizedCode_injective n G D r)
  apply (hinj.trans hc).trans
  have hcost := caseI_cost_mono C (∑ i : Fin (t+1),n i) B hB
  have hp0 : 0≤VerticalHallBase.polynomial r := by unfold VerticalHallBase.polynomial; positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcost hp0) (by positivity)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualChosenHistoryCaseI
