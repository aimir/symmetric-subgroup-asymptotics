import SymmetricSubgroupAsymptotics.MarkedC4ActualChosenHistorySchedule
import SymmetricSubgroupAsymptotics.MarkedC4ActualNormalPriorityTarget
import SymmetricSubgroupAsymptotics.MarkedC4ActualHistoryStepCount
import SymmetricSubgroupAsymptotics.MarkedC4ActualUniformEpiReserve

/-! Actual positive fixed-history recurrence. The target is constructed
from its canonical current normal; source rank/dN/reserve are derived for
EVERY actual raw suffix image. Only one suffix schedule is counted. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualChosenHistoryPositive
open ActualChosenHistorySchedule ActualHistoryPriority ActualAbelianFactorSplit
open RDTOriginalWordStructure RDTExcessStructure RDTNormalFInterface ActualNormalFMarkedPeel

variable {t : ℕ} (n : Fin (t+1) → ℕ)
  (G : ∀ i,Subgroup (Equiv.Perm (Fin (n i)))) (D : Data n G)
local notation "N" => ActualHistorySchedule.currentMenu (fun i => (G i : Type)) D.rows (fun i => D.normal i 0)
local instance normalAt (i : Fin (t+1)) : (N i).val.Normal := (N i).property
abbrev Quotients := fun i => G i ⧸ (N i).val

theorem card_le_suffix
    (hKP : KovacsPraegerBinaryAbelianQuotientBound) (h55 : PublishedTheorem55Binary)
    (h53 : ActualCaseIITargetStructure.PublishedProposition53Binary)
    (h57 : RDTExcessStructure.PublishedTheorem57Binary)
    (h8 : RDTDegreeEightExceptional.PublishedDegreeEightExceptional)
    (hderived : RDTDerivedNormalQuarter.PublishedDerivedNormalQuarterBinary)
    (lit : RDTTheorem46BinaryInput)
    (C : ℕ) (hcut : ∀ i,n i≤C) (hG : ∀ i,IsPGroup 2 (G i))
    (htrans : ∀ i,∀ x y : Fin (n i),∃ g : G i,g.val x=y)
    (hD : Chosen D)
    (hp : 0<normalPriority (n 0) (G 0) ⟨(D.rows 0).val 0,D.normal 0 0⟩)
    (B r : ℕ) (hB : (∑ i : Fin (t+1),n i)≤B) :
    (Nat.card (Family D (ActualGlobalMarkGeneratorRank.Marks r)) : ℝ)≤
      ActualUniformEpiReserve.peelFactor lit C B r*
        (2 : ℝ)^(markedF (∑ i : Fin (t+1),(n i : ℝ)) r-
          markedF (∑ j : Fin t,(n j.succ : ℝ)) r)*
            (Nat.card (Family (suffix D) (ActualGlobalMarkGeneratorRank.Marks r)) : ℝ) := by
  letI : Fintype (Family (suffix D) (ActualGlobalMarkGeneratorRank.Marks r)) := Fintype.ofFinite _
  change 0<normalPriority (n 0) (G 0) (N 0) at hp
  have hnonab : ¬∀ x y : (Quotients n G D) 0,x*y=y*x := by
    by_contra hab
    change ∀ x y : G 0 ⧸ (N 0).val,x*y=y*x at hab
    unfold normalPriority at hp
    split_ifs at hp with hn
    all_goals first | exact hn hab | omega
  letI : Nontrivial ((Quotients n G D) 0) := not_subsingleton_iff_nontrivial.mp (by
    intro hs
    letI := hs
    exact hnonab (fun _ _ => Subsingleton.elim _ _))
  obtain ⟨TQ,e,hTQ,hbranch,hexcess,hzcap⟩ := ActualNormalPriorityTarget.target_packet
    h53 h57 h8 (n 0) (G 0) (hG 0) (htrans 0) (N 0) hp
  have hsbranch : e=3 ∨
      (e=5/4 ∧ ∀ j : Fin t,¬Abelian (fun j => (Quotients n G D) j.succ) j →
        ¬(HasExcess (G j.succ) (n j.succ) 2 ∧ n j.succ=8)) ∨
      (e=1 ∧ ∀ j : Fin t,¬Abelian (fun j => (Quotients n G D) j.succ) j →
        ¬HasExcess (G j.succ) (n j.succ) 2) := by
    rcases hbranch with ⟨hhead,he⟩|⟨hhead,he⟩|⟨hhead,he⟩
    · exact Or.inl he
    · refine Or.inr (Or.inl ⟨he,?_⟩)
      intro j hab hbad
      change ¬∀ x y : G j.succ ⧸ (N j.succ).val,x*y=y*x at hab
      have hj : normalPriority (n j.succ) (G j.succ) (N j.succ)=3 := by
        simp only [normalPriority,if_pos hab,if_pos hbad.1,if_pos hbad.2]
      have hm := hD 0 j.succ (Nat.zero_le _)
      change normalPriority (n j.succ) (G j.succ) (N j.succ)≤normalPriority (n 0) (G 0) (N 0) at hm
      rw [hj,hhead] at hm
      omega
    · refine Or.inr (Or.inr ⟨he,?_⟩)
      intro j hab hbad
      change ¬∀ x y : G j.succ ⧸ (N j.succ).val,x*y=y*x at hab
      have hj : 2≤normalPriority (n j.succ) (G j.succ) (N j.succ) := by
        rw [normalPriority,if_pos hab,if_pos hbad]
        split_ifs <;> norm_num
      have hm := hD 0 j.succ (Nat.zero_le _)
      change normalPriority (n j.succ) (G j.succ) (N j.succ)≤normalPriority (n 0) (G 0) (N 0) at hm
      rw [hhead] at hm
      omega
  have hQ : IsPGroup 2 ((Quotients n G D) 0) :=
    (hG 0).of_surjective (QuotientGroup.mk' (N 0).val) (QuotientGroup.mk'_surjective _)
  have hQcard : Nat.card ((Quotients n G D) 0)≤2^(2+C) := by
    have hi := hcut 0
    exact (ActualBinaryPhysicalOrderBudget.quotient_card_le (G 0) (hG 0)
      (QuotientGroup.mk' (N 0).val) (QuotientGroup.mk'_surjective _)).trans
        (pow_le_pow_right₀ (by norm_num : 1≤(2 : ℕ)) (by omega : n 0≤2+C))
  have hsum : (∑ i : Fin (t+1),(n i : ℝ))=(n 0 : ℝ)+∑ j : Fin t,(n j.succ : ℝ) :=
    Fin.sum_univ_succ _
  have hBtail : (∑ j : Fin t,(n j.succ : ℝ))≤(B : ℝ) := by
    have hh : (∑ i : Fin (t+1),(n i : ℝ))≤(B : ℝ) := by exact_mod_cast hB
    have hn0 : (0 : ℝ)≤n 0 := Nat.cast_nonneg _
    linarith
  have hterm (E : Family (suffix D) (ActualGlobalMarkGeneratorRank.Marks r)) :
      (Nat.card (ActualIsolatedFreeEpimorphism.Family ((Quotients n G D) 0)
        (ActualHistoryStepCount.imageFamily (fun i => ↥(G i)) (ActualGlobalMarkGeneratorRank.Marks r)
          D.rows (fun i => D.normal i 0) E).val) : ℝ)≤
      ActualUniformEpiReserve.peelFactor lit C B r*
        (2 : ℝ)^(markedF (∑ i : Fin (t+1),(n i : ℝ)) r-
          markedF (∑ j : Fin t,(n j.succ : ℝ)) r) := by
    let A := ActualHistoryStepCount.imageFamily (fun i => ↥(G i)) (ActualGlobalMarkGeneratorRank.Marks r)
      D.rows (fun i => D.normal i 0) E
    have hbound := ActualUniformEpiReserve.actual_epi_le_uniform_reserve hKP h55 hderived lit
      (fun j : Fin t => n j.succ) (fun j => G j.succ) C (fun j => hcut j.succ)
      (fun j => hG j.succ) (fun j => htrans j.succ) (fun j => (Quotients n G D) j.succ)
      (fun j => QuotientGroup.mk' (N j.succ).val) (fun j => QuotientGroup.mk'_surjective _)
      r A.val A.property ((Quotients n G D) 0) hQ hQcard TQ hTQ e (n 0)
      hexcess hzcap hsbranch B hBtail
    have hcard : (Nat.card (ActualIsolatedFreeEpimorphism.Family ((Quotients n G D) 0) A.val) : ℝ)≤
        Nat.card {f : A.val →* (Quotients n G D) 0 // Function.Surjective f} := by
      exact_mod_cast ActualIsolatedFreeEpimorphism.card_le ((Quotients n G D) 0) A.val
    have hw : (∑ j : Fin t,(n j.succ : ℝ))+(n 0 : ℝ)=∑ i : Fin (t+1),(n i : ℝ) := by linarith
    exact hcard.trans (by simpa only [hw] using hbound)
  have hstep := ActualHistoryStepCount.card_le_sum_epi (fun i => ↥(G i))
    (ActualGlobalMarkGeneratorRank.Marks r) D.rows (fun i => D.normal i 0)
  have hr : (Nat.card (Family D (ActualGlobalMarkGeneratorRank.Marks r)) : ℝ)≤
      ∑ E : Family (suffix D) (ActualGlobalMarkGeneratorRank.Marks r),
        (Nat.card (ActualIsolatedFreeEpimorphism.Family ((Quotients n G D) 0)
          (ActualHistoryStepCount.imageFamily (fun i => ↥(G i)) (ActualGlobalMarkGeneratorRank.Marks r)
            D.rows (fun i => D.normal i 0) E).val) : ℝ) := by exact_mod_cast hstep
  apply hr.trans
  calc
    _≤∑ _E : Family (suffix D) (ActualGlobalMarkGeneratorRank.Marks r),
      ActualUniformEpiReserve.peelFactor lit C B r*
        (2 : ℝ)^(markedF (∑ i : Fin (t+1),(n i : ℝ)) r-
          markedF (∑ j : Fin t,(n j.succ : ℝ)) r) := Finset.sum_le_sum (fun E _ => hterm E)
    _=_ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]; ring

end SymmetricSubgroupAsymptotics.MarkedC4.ActualChosenHistoryPositive
