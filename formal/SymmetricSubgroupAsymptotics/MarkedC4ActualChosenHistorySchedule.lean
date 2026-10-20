import SymmetricSubgroupAsymptotics.MarkedC4ActualHistoryPriority
import SymmetricSubgroupAsymptotics.MarkedC4ActualHistorySchedule
import SymmetricSubgroupAsymptotics.MarkedC4ActualExcessHistoryUniversal

/-! A fixed original normal-chain schedule carries only structural finite
selection conditions. Its chosen-head property survives taking a suffix;
all actual subgroups in the schedule have the SAME current priorities. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualChosenHistorySchedule
open ActualHistoryPriority ActualPeelNormalChains ActualExcessHistorySelection

structure Data {t : ℕ} (n : Fin t → ℕ)
    (G : ∀ i,Subgroup (Equiv.Perm (Fin (n i)))) where
  rows : ActualQuotientTableauMenus.RowMenu (fun i => ↥(G i))
  normal : ∀ i m,((rows i).val m).Normal

def Chosen {t : ℕ} {n : Fin t → ℕ} {G : ∀ i,Subgroup (Equiv.Perm (Fin (n i)))}
    (D : Data n G) : Prop :=
  ∀ m i : Fin t,m.val ≤ i.val →
    normalPriority (n i) (G i) ⟨(D.rows i).val m,D.normal i m⟩≤
      normalPriority (n m) (G m) ⟨(D.rows m).val m,D.normal m m⟩

abbrev Family {t : ℕ} {n : Fin t → ℕ} {G : ∀ i,Subgroup (Equiv.Perm (Fin (n i)))}
    (D : Data n G) (M : Type) [Group M] :=
  {J : ActualFullPhysicalWordPeel.Family (fun i => ↥(G i)) M //
    normalChains (fun i => ↥(G i)) J.val 1=D.rows}

variable {t : ℕ} {n : Fin (t+1) → ℕ}
  {G : ∀ i,Subgroup (Equiv.Perm (Fin (n i)))}

def suffix (D : Data n G) : Data (fun j : Fin t => n j.succ) (fun j => G j.succ) where
  rows := ActualHistorySchedule.suffix (fun i => ↥(G i)) D.rows
  normal j m := D.normal j.succ m.succ

theorem chosen_suffix (D : Data n G) (hD : Chosen D) : Chosen (suffix D) := by
  intro m i hmi
  exact hD m.succ i.succ (by change m.val+1 ≤ i.val+1; omega)

theorem priority_eq_current (D : Data n G) (M : Type) [Group M]
    (J : Family D M) (i : Fin (t+1)) :
    priority n G M J.val.val J.val.property Finset.univ i=
      normalPriority (n i) (G i) ⟨(D.rows i).val 0,D.normal i 0⟩ := by
  rw [priority_eq_normal]
  apply congrArg (normalPriority (n i) (G i))
  apply Subtype.ext
  have hh := congrArg
    (fun rows : ActualQuotientTableauMenus.RowMenu (fun i => ↥(G i)) => (rows i).val 0) J.property
  change factor (fun i => ↥(G i)) J.val.val (remaining 1 0) i=(D.rows i).val 0 at hh
  have hrem : remaining (1 : Equiv.Perm (Fin (t+1))) 0=Finset.univ := by
    ext j
    simp [remaining]
  simpa only [hrem] using hh

theorem head_maximum (D : Data n G) (hD : Chosen D) (M : Type) [Group M]
    (J : Family D M) :
    ∀ i∈(Finset.univ : Finset (Fin (t+1))),
      priority n G M J.val.val J.val.property Finset.univ i≤
        priority n G M J.val.val J.val.property Finset.univ 0 := by
  intro i hi
  rw [priority_eq_current,priority_eq_current]
  exact hD 0 i (Nat.zero_le _)

/-- The actual stopping branch, with no restriction on small original
physical degrees; their quotients belong to the abelian block. -/
theorem stop_caseI (h53 : ActualCaseIITargetStructure.PublishedProposition53Binary)
    (hG : ∀ i,IsPGroup 2 (G i))
    (htrans : ∀ i,∀ x y : Fin (n i),∃ g : G i,g.val x=y)
    (D : Data n G) (hD : Chosen D) (M : Type) [Group M] (J : Family D M)
    (hz : normalPriority (n 0) (G 0) ⟨(D.rows 0).val 0,D.normal 0 0⟩=0) :
    ∀ i∈(Finset.univ : Finset (Fin (t+1))),
      Nonabelian n G M J.val.val J.val.property Finset.univ i →
      ∀ V : Subgroup (ActualExcessHistorySelection.Quotient n G M J.val.val
        J.val.property Finset.univ i),V.Normal →(normalGen V : ℝ)≤(n i : ℝ)/4 := by
  apply ActualExcessHistoryUniversal.caseI_of_zero n G M J.val.val J.val.property h53 hG htrans
  intro i hi
  have hm := head_maximum D hD M J i hi
  rw [priority_eq_current,priority_eq_current,hz] at hm
  rw [priority_eq_current]
  exact Nat.eq_zero_of_le_zero hm

end SymmetricSubgroupAsymptotics.MarkedC4.ActualChosenHistorySchedule
