import SymmetricSubgroupAsymptotics.MarkedC4ActualHistorySuffix
import SymmetricSubgroupAsymptotics.MarkedC4ActualFixedNormalWordPeel

/-! Fixed ORIGINAL normal-chain schedules are closed under a raw physical
peel. This carries the global menu into the smaller source without charging
another menu and identifies the current normalization menu exactly. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualHistorySchedule
open ActualPeelNormalChains ActualQuotientTableauMenus ActualFullPhysicalWordPeel

variable {t : ℕ} (F : Fin (t+1) → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (M : Type) [Group M]

def suffix (R : RowMenu F) : RowMenu (TailFactors F) := fun j =>
  ⟨fun m => (R j.succ).val m.succ,by
    intro m n hmn
    apply (R j.succ).property
    change m.val+1≤n.val+1
    exact Nat.add_le_add_right hmn 1⟩

abbrev Family (R : RowMenu F) := {J : ActualFullPhysicalWordPeel.Family F M //
  normalChains F J.val 1=R}

theorem chains_suffix (J : Subgroup ((∀ i,F i) × M)) :
    normalChains (TailFactors F) (ActualHistorySuffix.source F M J) 1=
      suffix F (normalChains F J 1) := by
  funext j
  apply Subtype.ext
  funext m
  exact ActualHistorySuffix.factor_suffix F M J m.val j

def tail (R : RowMenu F) (J : Family F M R) :
    {E : ActualFullPhysicalWordPeel.Family (TailFactors F) M //
      normalChains (TailFactors F) E.val 1=suffix F R} := by
  let E := ActualHistorySuffix.source F M J.val.val
  have hfull (j : Fin t) : Function.Surjective (fun h : E => h.val.1 j) := by
    intro g
    obtain ⟨h,hh⟩ := J.val.property j.succ g
    exact ⟨⟨ActualHistorySuffix.tailMap F M h.val,⟨h.val,h.property,rfl⟩⟩,hh⟩
  refine ⟨⟨E,hfull⟩,?_⟩
  exact (chains_suffix F M J.val.val).trans (congrArg (suffix F) J.property)

def currentMenu (R : RowMenu F) (hN : ∀ i,((R i).val 0).Normal) :
    ActualWholeWordPackets.Menu F := fun i => ⟨(R i).val 0,hN i⟩

theorem actualMenu_eq (R : RowMenu F) (hN : ∀ i,((R i).val 0).Normal)
    (J : Family F M R) :
    ActualWholeWordPackets.actualMenu F M J.val=currentMenu F R hN := by
  funext i
  apply Subtype.ext
  have hh := congrArg (fun rows : RowMenu F => (rows i).val 0) J.property
  change factor F J.val.val (remaining 1 0) i=(R i).val 0 at hh
  have hrem : remaining (1 : Equiv.Perm (Fin (t+1))) 0=Finset.univ := by
    ext j
    simp [remaining]
  rw [hrem] at hh
  exact hh

/-- Feed the current exact menu to the actual normalized epi decoder.
The next raw source already belongs to `suffix R` by `tail`. -/
def fixedStage (R : RowMenu F) (hN : ∀ i,((R i).val 0).Normal)
    (J : Family F M R) :
    ActualFixedNormalWordPeel.Family F M (currentMenu F R hN) :=
  ⟨J.val,actualMenu_eq F M R hN J⟩

theorem fixedStage_injective (R : RowMenu F) (hN : ∀ i,((R i).val 0).Normal) :
    Function.Injective (fixedStage F M R hN) := by
  intro J K h
  apply Subtype.ext
  exact congrArg
    (fun H : ActualFixedNormalWordPeel.Family F M (currentMenu F R hN) => H.val) h

end SymmetricSubgroupAsymptotics.MarkedC4.ActualHistorySchedule
