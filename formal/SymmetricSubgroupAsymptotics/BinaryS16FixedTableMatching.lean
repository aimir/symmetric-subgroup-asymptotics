import SymmetricSubgroupAsymptotics.BinaryS16DirectPhysicalTarget
import SymmetricSubgroupAsymptotics.BinaryS16RecordedBlockRecovery

/-!
# Recorded-block matching on one fixed S16 support fibre

`BinaryS16RecordedBlockRecovery` proves the semantic matching theorem with a
single common padding length.  The concrete fixed-support encoder obtains its
table by casting each subgroup's exact old-support table to that common
length.  This file removes precisely those two casts.  Thus equality of the
actual `blocks` keys already matches recorded source orbits, their complete
records, and their literal ambient point sets.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16FixedTableMatching

open SymmetricSubgroupAsymptotics
open BinaryDegreeEightPhysicalDecoration
open BinaryDegreeEightSixteenPhysicalDecoration
open BinaryS16CanonicalCarrierProfile
open BinaryS16CanonicalMixedBlockTable
open BinaryS16DirectFixedSupportClosure
open BinaryS16RecordedBlockRecovery

variable {N : ℕ} (C : SupportIndex N)

abbrev Actual := BinaryS16DirectPhysicalTarget.Actual C

/-! ## Transporting the canonical padded table -/

/-- Casting the padding length of a canonical table only transports its
cardinality proof.  The ordered record family and every occupied entry remain
definitionally the same after eliminating the length equality. -/
theorem cast_canonicalMixedBlockTableOfRecords
    {Cold Cold' : ℕ} {I : Type*} [Fintype I]
    (key : I → Fin (2 * N))
    (hkey : Function.Injective key)
    (record : I → MixedBlockRecord N)
    (hrecord : ∀ i, (record i).leastPoint = key i)
    (hcount : Fintype.card I ≤ Cold)
    (hCold : Cold = Cold') :
    cast (congrArg (CanonicalMixedBlockTable N) hCold)
        (canonicalMixedBlockTableOfRecords
          key hkey record hrecord hcount) =
      canonicalMixedBlockTableOfRecords
        key hkey record hrecord (hCold ▸ hcount) := by
  subst Cold'
  rfl

/-- The record-count bound transported to the fixed support index. -/
def fixedRecordedOrbitCount (H : Actual C) :
    Fintype.card
        (RecordedOrbit
          (BinaryS16DirectPhysicalTarget.subgroup C H)
          (BinaryS16DirectPhysicalTarget.residualSector C H)) ≤ C.1.1 :=
  BinaryS16DirectPhysicalTarget.oldSupport_eq C H ▸
    recordedOrbit_card_le_oldSupport
      (BinaryS16DirectPhysicalTarget.subgroup C H)
      (BinaryS16DirectPhysicalTarget.residualSector C H)

/-- The exact record family written directly with the common fixed padding
length.  This is propositionally the same table as the cast used by the
concrete physical key. -/
def fixedTable (H : Actual C) : CanonicalMixedBlockTable N C.1.1 :=
  canonicalMixedBlockTableOfRecords
    (fun o : RecordedOrbit
        (BinaryS16DirectPhysicalTarget.subgroup C H)
        (BinaryS16DirectPhysicalTarget.residualSector C H) ↦
      orbitLeast (BinaryS16DirectPhysicalTarget.subgroup C H) o.1)
    (by
      intro o p hop
      exact Subtype.ext
        (orbitLeast_injective
          (BinaryS16DirectPhysicalTarget.subgroup C H) hop))
    (recordOf
      (BinaryS16DirectPhysicalTarget.subgroup C H)
      (BinaryS16DirectPhysicalTarget.residualSector C H))
    (recordOf_leastPoint
      (BinaryS16DirectPhysicalTarget.subgroup C H)
      (BinaryS16DirectPhysicalTarget.residualSector C H))
    (fixedRecordedOrbitCount C H)

/-- The casted table used in the concrete key equals the same canonical table
constructed directly at the fixed padding length. -/
theorem blocks_eq_fixedTable (H : Actual C) :
    BinaryS16DirectPhysicalTarget.blocks C H = fixedTable C H := by
  unfold BinaryS16DirectPhysicalTarget.blocks
  unfold BinaryS16CanonicalMixedBlockTable.table
  unfold fixedTable fixedRecordedOrbitCount
  exact cast_canonicalMixedBlockTableOfRecords
    (fun o : RecordedOrbit
        (BinaryS16DirectPhysicalTarget.subgroup C H)
        (BinaryS16DirectPhysicalTarget.residualSector C H) ↦
      orbitLeast (BinaryS16DirectPhysicalTarget.subgroup C H) o.1)
    (by
      intro o p hop
      exact Subtype.ext
        (orbitLeast_injective
          (BinaryS16DirectPhysicalTarget.subgroup C H) hop))
    (recordOf
      (BinaryS16DirectPhysicalTarget.subgroup C H)
      (BinaryS16DirectPhysicalTarget.residualSector C H))
    (recordOf_leastPoint
      (BinaryS16DirectPhysicalTarget.subgroup C H)
      (BinaryS16DirectPhysicalTarget.residualSector C H))
    (recordedOrbit_card_le_oldSupport
      (BinaryS16DirectPhysicalTarget.subgroup C H)
      (BinaryS16DirectPhysicalTarget.residualSector C H))
    (BinaryS16DirectPhysicalTarget.oldSupport_eq C H)

/-! ## The concrete fixed-key matching theorem -/

/-- Equality of the concrete fixed-support block keys matches every recorded
source orbit on the left with a unique recorded orbit on the right.  Besides
the sorting key and full route record, the conclusion includes equality of
the original labelled point sets. -/
theorem matching_recordedOrbit_of_blocks_eq
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalTarget.blocks C H =
      BinaryS16DirectPhysicalTarget.blocks C K)
    (o : RecordedOrbit
      (BinaryS16DirectPhysicalTarget.subgroup C H)
      (BinaryS16DirectPhysicalTarget.residualSector C H)) :
    ∃! p : RecordedOrbit
        (BinaryS16DirectPhysicalTarget.subgroup C K)
        (BinaryS16DirectPhysicalTarget.residualSector C K),
      orbitLeast (BinaryS16DirectPhysicalTarget.subgroup C K) p.1 =
          orbitLeast (BinaryS16DirectPhysicalTarget.subgroup C H) o.1 ∧
        recordOf
            (BinaryS16DirectPhysicalTarget.subgroup C K)
            (BinaryS16DirectPhysicalTarget.residualSector C K) p =
          recordOf
            (BinaryS16DirectPhysicalTarget.subgroup C H)
            (BinaryS16DirectPhysicalTarget.residualSector C H) o ∧
        p.1.orbit = o.1.orbit := by
  have hfixed : fixedTable C H = fixedTable C K :=
    (blocks_eq_fixedTable C H).symm.trans
      (hblocks.trans (blocks_eq_fixedTable C K))
  apply matching_recordedOrbit_of_table_eq
    (BinaryS16DirectPhysicalTarget.subgroup C H)
    (BinaryS16DirectPhysicalTarget.residualSector C H)
    (BinaryS16DirectPhysicalTarget.residualSector C K)
    (fixedRecordedOrbitCount C H)
    (fixedRecordedOrbitCount C K)
  simpa only [fixedTable] using hfixed

end SymmetricSubgroupAsymptotics.BinaryS16FixedTableMatching

end
