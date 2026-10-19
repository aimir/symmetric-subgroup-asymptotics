import SymmetricSubgroupAsymptotics.MarkedC4ActualHistorySchedule
import SymmetricSubgroupAsymptotics.MarkedC4ActualMarkedWordPullback

/-! The per-step epi source is EXACTLY the image of the raw suffix source
under the CURRENT fixed normal quotients. Its next original chain schedule
is already fixed, so no new source-menu sum is introduced. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualFixedHistorySource
open ActualWholeWordPackets ActualFixedNormalWordPeel

variable {t : ℕ} (F : Fin (t+1) → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (M : Type) [Group M] (N : Menu F)
local instance normalAt (i : Fin (t+1)) : (N i).val.Normal := (N i).property

def tailMenu : Menu (ActualFullPhysicalWordPeel.TailFactors F) := fun j => N j.succ

def tailQuotientMap :
    ((∀ j,ActualFullPhysicalWordPeel.TailFactors F j) × M) →*
      ((∀ j,ActualFullPhysicalWordPeel.TailFactors (Factors F N) j) × M) :=
  ActualWholeWordPackets.quotientMap (ActualFullPhysicalWordPeel.TailFactors F) M (tailMenu F N)

theorem normalize_is_map (J : ActualFixedNormalWordPeel.Family F M N) :
    (normalize F M N J).val.val=J.val.val.map (ActualWholeWordPackets.quotientMap F M N) := by
  rcases J with ⟨J,hJ⟩
  cases hJ
  change ActualWholeWordNormalization.normalized F M J=J.val.map _
  unfold ActualWholeWordNormalization.normalized
  congr 1

/-- Same-source identity connecting the actual epi packet with the raw
original suffix, keeping all vertical marker information. -/
theorem epi_source_eq_raw_image (J : ActualFixedNormalWordPeel.Family F M N) :
    ActualNormalizedWordPeel.Source (Factors F N) M (normalize F M N J)=
      (ActualHistorySuffix.source F M J.val.val).map (tailQuotientMap F M N) := by
  change (((normalize F M N J).val.val.map
    (ActualFullPhysicalWordPeel.split (Factors F N) M).toMonoidHom).map
      (MonoidHom.snd _ _))=_
  rw [normalize_is_map]
  unfold ActualHistorySuffix.source
  rw [Subgroup.map_map,Subgroup.map_map,Subgroup.map_map]
  congr 1

/-- The raw source has the prescribed next schedule, while its image is
the literal source of the normalized epi fibre. Both objects are retained. -/
theorem scheduled_epi_source
    (R : ActualQuotientTableauMenus.RowMenu F)
    (hN : ∀ i,((R i).val 0).Normal)
    (J : ActualHistorySchedule.Family F M R) :
    ActualNormalizedWordPeel.Source
      (Factors F (ActualHistorySchedule.currentMenu F R hN)) M
      (normalize F M (ActualHistorySchedule.currentMenu F R hN)
        (ActualHistorySchedule.fixedStage F M R hN J))=
      ((ActualHistorySchedule.tail F M R J).val.val).map
        (tailQuotientMap F M (ActualHistorySchedule.currentMenu F R hN)) :=
  epi_source_eq_raw_image F M (ActualHistorySchedule.currentMenu F R hN)
    (ActualHistorySchedule.fixedStage F M R hN J)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualFixedHistorySource
