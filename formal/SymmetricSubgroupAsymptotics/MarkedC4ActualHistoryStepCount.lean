import SymmetricSubgroupAsymptotics.MarkedC4ActualFixedHistorySource

/-! Exact per-step fixed-history count: sum over the SAME raw suffix
history family, with the actual epi fibre of its fixed quotient image.
There is no fresh normal-menu sum and no numerical counting callback. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualHistoryStepCount
open ActualWholeWordPackets ActualFullPhysicalWordPeel

variable {t : ℕ} (F : Fin (t+1) → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (M : Type) [Group M] (R : ActualQuotientTableauMenus.RowMenu F)
  (hN : ∀ i,((R i).val 0).Normal)
local notation "N" => ActualHistorySchedule.currentMenu F R hN
local instance normalAt (i : Fin (t+1)) : (N i).val.Normal := (N i).property
abbrev Quotients := Factors F N
abbrev SuffixFamily := {E : ActualFullPhysicalWordPeel.Family (TailFactors F) M //
  ActualPeelNormalChains.normalChains (TailFactors F) E.val 1=ActualHistorySchedule.suffix F R}
local instance suffixFintype [Finite M] : Fintype (SuffixFamily F M R) := Fintype.ofFinite _

def imageFamily (E : SuffixFamily F M R) :
    ActualFullPhysicalWordPeel.Family (TailFactors (Quotients F R hN)) M := by
  refine ⟨E.val.val.map (ActualFixedHistorySource.tailQuotientMap F M N),?_⟩
  intro j g
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (N j.succ).val g
  obtain ⟨e,he⟩ := E.val.property j x
  exact ⟨⟨ActualFixedHistorySource.tailQuotientMap F M N e.val,⟨e.val,e.property,rfl⟩⟩,
    congrArg (QuotientGroup.mk' (N j.succ).val) he⟩

def Packet := Σ E : SuffixFamily F M R,
  {p : ActualNormalizedWordPeel.Packet (Quotients F R hN) M //p.1.val=(imageFamily F M R hN E).val}

def code (J : ActualHistorySchedule.Family F M R) : Packet F M R hN :=
  ⟨ActualHistorySchedule.tail F M R J,
    ActualFixedNormalWordPeel.code F M N (ActualHistorySchedule.fixedStage F M R hN J),
    ActualFixedHistorySource.scheduled_epi_source F M R hN J⟩

theorem code_injective : Function.Injective (code F M R hN) := by
  intro J K he
  apply ActualHistorySchedule.fixedStage_injective F M R hN
  apply ActualFixedNormalWordPeel.code_injective F M N
  exact congrArg (fun p : Packet F M R hN => p.2.val) he

/-- The redundant actual-source field is determined by the raw suffix;
its exact fibre is the epi family of that one actual image. -/
def fibreEquiv (E : SuffixFamily F M R) :
    {p : ActualNormalizedWordPeel.Packet (Quotients F R hN) M //
      p.1.val=(imageFamily F M R hN E).val} ≃
    ActualIsolatedFreeEpimorphism.Family ((Quotients F R hN) 0) (imageFamily F M R hN E).val where
  toFun p := by
    have h : p.val.1=imageFamily F M R hN E := Subtype.ext p.property
    exact h ▸ p.val.2
  invFun f := ⟨⟨imageFamily F M R hN E,f⟩,rfl⟩
  left_inv p := by
    rcases p with ⟨⟨A,f⟩,hA⟩
    have h : A=imageFamily F M R hN E := Subtype.ext hA
    subst A
    rfl
  right_inv _ := rfl

def packetEquiv : Packet F M R hN ≃
    Σ E : SuffixFamily F M R,
      ActualIsolatedFreeEpimorphism.Family ((Quotients F R hN) 0) (imageFamily F M R hN E).val :=
  Equiv.sigmaCongrRight (fun E => fibreEquiv F M R hN E)

instance packetFinite [Finite M] : Finite (Packet F M R hN) := by
  unfold Packet
  infer_instance

/-- The actual fixed-menu one-step recurrence, before applying the
ordinary4.6 marked reserve bound to each actual source image. -/
theorem card_le_sum_epi [Finite M] :
    Nat.card (ActualHistorySchedule.Family F M R)≤
      ∑ E : SuffixFamily F M R,
        Nat.card (ActualIsolatedFreeEpimorphism.Family ((Quotients F R hN) 0)
          (imageFamily F M R hN E).val) := by
  letI : Fintype (SuffixFamily F M R) := Fintype.ofFinite _
  letI : ∀ E : SuffixFamily F M R,Fintype
    (ActualIsolatedFreeEpimorphism.Family ((Quotients F R hN) 0)
      (imageFamily F M R hN E).val) := fun _ => Fintype.ofFinite _
  calc
    _≤Nat.card (Packet F M R hN) :=
      Nat.card_le_card_of_injective (code F M R hN) (code_injective F M R hN)
    _=_ := by
      rw [Nat.card_congr (packetEquiv F M R hN),Nat.card_eq_fintype_card,Fintype.card_sigma]
      simp only [Nat.card_eq_fintype_card]

end SymmetricSubgroupAsymptotics.MarkedC4.ActualHistoryStepCount
