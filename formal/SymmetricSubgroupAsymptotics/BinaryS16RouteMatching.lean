import SymmetricSubgroupAsymptotics.BinaryS16RouteSlotSkeleton
import SymmetricSubgroupAsymptotics.BinaryS16SourceOrbitRecordStatus
import SymmetricSubgroupAsymptotics.BinaryS16SourceOrbitReindex

/-!
# Matching the S16 route skeleton across a physical key fibre

The source-orbit reindexing preserves the literal mixed record.  Consequently
it preserves the four-valued proper-carrier discriminator before any
dependent quotient type is compared.  Proper occurrences therefore use the
same fixed exceptional slot; every other occurrence exposes a literal
quotient-identity presentation on both sides.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16RouteMatching

open SymmetricSubgroupAsymptotics
open BinaryCarrierMenuSlots
open BinaryS16DirectPhysicalEncoding
open BinaryS16DirectPhysicalTarget
open BinaryS16JointOrbitData
open BinaryS16RouteSlotSkeleton
open BinaryS16SourceOrbitRecordStatus
open BinaryS16SourceOrbitReindex

variable {N : ℕ} (C : BinaryS16DirectFixedSupportClosure.SupportIndex N)

abbrev Actual := BinaryS16DirectPhysicalTarget.Actual C

/-- The proper-carrier discriminator is invariant under the exact occurrence
reindexing furnished by equality of the two physical keys. -/
theorem properKindAt_occurrenceEquiv
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K)
    (q : Occurrence C H) :
    properKindAt (subgroup C K) (residualSector C K)
        (occurrenceEquiv C hblocks htarget q).1 =
      properKindAt (subgroup C H) (residualSector C H) q.1 := by
  unfold properKindAt
  rw [occurrenceEquiv_fst C hblocks htarget q]
  rw [sourceOrbitEquiv_recordAt C hblocks htarget q.1]

/-- If one side uses a proper carrier, both routed occurrences are literally
the same one of the four exceptional slots. -/
theorem matched_proper_slots
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K)
    (q : Occurrence C H) (e : Exceptional)
    (hkind : properKindAt (subgroup C H) (residualSector C H) q.1 = some e) :
    (BinaryS16JointAxisRouting.axisRouting
        (subgroup C H) (residualSector C H) q).axisSlot.slot =
        exceptionalSlot e ∧
      (BinaryS16JointAxisRouting.axisRouting
        (subgroup C K) (residualSector C K)
        (occurrenceEquiv C hblocks htarget q)).axisSlot.slot =
        exceptionalSlot e := by
  have hkindK : properKindAt (subgroup C K) (residualSector C K)
      (occurrenceEquiv C hblocks htarget q).1 = some e := by
    rw [properKindAt_occurrenceEquiv C hblocks htarget q]
    exact hkind
  have extract
      (L : Actual C) (r : Occurrence C L)
      (hr : properKindAt (subgroup C L) (residualSector C L) r.1 = some e) :
      (BinaryS16JointAxisRouting.axisRouting
        (subgroup C L) (residualSector C L) r).axisSlot.slot =
          exceptionalSlot e := by
    rcases axisRouting_proper_or_noProper
      (subgroup C L) (residualSector C L) r with hproper | hnone
    · obtain ⟨e',he',hslot⟩ := hproper
      have : e' = e := Option.some.inj (he'.symm.trans hr)
      simpa only [this] using hslot
    · rw [hr] at hnone
      contradiction
  exact ⟨extract H q hkind,
    extract K (occurrenceEquiv C hblocks htarget q) hkindK⟩

/-- In the complementary branch both matched routes retain their actual
normal subgroup as a quotient-identity presentation. -/
def matched_identityPresentations
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K)
    (q : Occurrence C H)
    (hkind : properKindAt (subgroup C H) (residualSector C H) q.1 = none) :
    IdentityPresentation
        (BinaryS16JointAxisRouting.axisRouting
          (subgroup C H) (residualSector C H) q).axisSlot.slot ×
      IdentityPresentation
        (BinaryS16JointAxisRouting.axisRouting
          (subgroup C K) (residualSector C K)
          (occurrenceEquiv C hblocks htarget q)).axisSlot.slot := by
  have hkindK : properKindAt (subgroup C K) (residualSector C K)
      (occurrenceEquiv C hblocks htarget q).1 = none := by
    rw [properKindAt_occurrenceEquiv C hblocks htarget q]
    exact hkind
  exact
    ⟨axisRouting_identityPresentation_of_properKindAt_eq_none
        (subgroup C H) (residualSector C H) q hkind,
      axisRouting_identityPresentation_of_properKindAt_eq_none
        (subgroup C K) (residualSector C K)
        (occurrenceEquiv C hblocks htarget q) hkindK⟩

end SymmetricSubgroupAsymptotics.BinaryS16RouteMatching

end
