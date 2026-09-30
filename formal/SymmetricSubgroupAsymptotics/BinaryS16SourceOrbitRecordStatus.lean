import SymmetricSubgroupAsymptotics.BinaryS16SourceOrbitPartition

/-!
# Recorded status under the S16 source-orbit matching

The source-orbit equivalence obtained from equality of the two concrete keys
preserves the recorded/unrecorded split.  In the recorded branch it also
preserves the complete mixed route record, not merely its sorting key or its
degree discriminator.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16SourceOrbitRecordStatus

open SymmetricSubgroupAsymptotics
open BinaryS16CanonicalMixedBlockTable
open BinaryS16DirectPhysicalEncoding
open BinaryS16DirectPhysicalTarget
open BinaryS16FixedTableMatching
open BinaryS16SourceOrbitPartition

variable {N : ℕ} (C : BinaryS16DirectFixedSupportClosure.SupportIndex N)

abbrev Actual := BinaryS16DirectPhysicalTarget.Actual C

/-- A recorded source orbit remains recorded after applying the literal
source-orbit equivalence, and its complete mixed route record is unchanged. -/
theorem sourceOrbitEquiv_recorded
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K)
    (o : OrbitProfileFromOrbits.Orbit (subgroup C H))
    (ho : (recordAt (subgroup C H) (residualSector C H) o).isSome) :
    ∃ hp : (recordAt (subgroup C K) (residualSector C K)
        ((sourceOrbitEquiv C hblocks htarget) o)).isSome,
      recordOf (subgroup C K) (residualSector C K)
          ⟨(sourceOrbitEquiv C hblocks htarget) o,hp⟩ =
        recordOf (subgroup C H) (residualSector C H) ⟨o,ho⟩ := by
  have hblocksTarget : BinaryS16DirectPhysicalTarget.blocks C H =
      BinaryS16DirectPhysicalTarget.blocks C K := by
    simpa only [BinaryS16DirectPhysicalEncoding.blocks,
      BinaryS16DirectPhysicalEncoding.rawBlocks,
      BinaryS16DirectPhysicalTarget.blocks] using hblocks
  obtain ⟨p,hp,_hp_unique⟩ := matching_recordedOrbit_of_blocks_eq C
    hblocksTarget
    (⟨o,ho⟩ : RecordedOrbit (subgroup C H) (residualSector C H))
  have hpo : p.1 = (sourceOrbitEquiv C hblocks htarget) o :=
    MulAction.orbitRel.Quotient.orbit_injective
      (hp.2.2.trans (sourceOrbitEquiv_orbit C hblocks htarget o).symm)
  let hp' : (recordAt (subgroup C K) (residualSector C K)
      ((sourceOrbitEquiv C hblocks htarget) o)).isSome := hpo ▸ p.2
  refine ⟨hp',?_⟩
  have hsub :
      (⟨(sourceOrbitEquiv C hblocks htarget) o,hp'⟩ :
        RecordedOrbit (subgroup C K) (residualSector C K)) = p := by
    apply Subtype.ext
    exact hpo.symm
  rw [hsub]
  exact hp.2.1

/-- The optional record itself is invariant under the source-orbit
equivalence.  This packages both recordedness and equality of the complete
record in the form most convenient for route case splits. -/
theorem sourceOrbitEquiv_recordAt
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K)
    (o : OrbitProfileFromOrbits.Orbit (subgroup C H)) :
    recordAt (subgroup C K) (residualSector C K)
        ((sourceOrbitEquiv C hblocks htarget) o) =
      recordAt (subgroup C H) (residualSector C H) o := by
  by_cases ho : (recordAt (subgroup C H) (residualSector C H) o).isSome
  · obtain ⟨hp,hrecord⟩ := sourceOrbitEquiv_recorded C
      hblocks htarget o ho
    calc
      recordAt (subgroup C K) (residualSector C K)
          ((sourceOrbitEquiv C hblocks htarget) o) =
          some (recordOf (subgroup C K) (residualSector C K)
            ⟨(sourceOrbitEquiv C hblocks htarget) o,hp⟩) :=
        Option.eq_some_of_isSome hp
      _ = some (recordOf (subgroup C H) (residualSector C H) ⟨o,ho⟩) :=
        congrArg some hrecord
      _ = recordAt (subgroup C H) (residualSector C H) o :=
        (Option.eq_some_of_isSome ho).symm
  · have hleft : recordAt (subgroup C H) (residualSector C H) o = none :=
      Option.not_isSome_iff_eq_none.mp ho
    have hright : recordAt (subgroup C K) (residualSector C K)
        ((sourceOrbitEquiv C hblocks htarget) o) = none := by
      apply Option.not_isSome_iff_eq_none.mp
      intro hp
      have hblocksTarget : BinaryS16DirectPhysicalTarget.blocks C H =
          BinaryS16DirectPhysicalTarget.blocks C K := by
        simpa only [BinaryS16DirectPhysicalEncoding.blocks,
          BinaryS16DirectPhysicalEncoding.rawBlocks,
          BinaryS16DirectPhysicalTarget.blocks] using hblocks
      obtain ⟨q,hq,_hq_unique⟩ := matching_recordedOrbit_of_blocks_eq C
        hblocksTarget.symm
        (⟨(sourceOrbitEquiv C hblocks htarget) o,hp⟩ :
          RecordedOrbit (subgroup C K) (residualSector C K))
      have hqo : q.1 = o :=
        MulAction.orbitRel.Quotient.orbit_injective
          (hq.2.2.trans (sourceOrbitEquiv_orbit C hblocks htarget o))
      exact ho (hqo ▸ q.2)
    exact hright.trans hleft.symm

/-- In particular, the omitted one-cell branch is preserved by the matched
source-orbit equivalence. -/
theorem sourceOrbitEquiv_unrecorded
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K)
    (o : OrbitProfileFromOrbits.Orbit (subgroup C H))
    (ho : recordAt (subgroup C H) (residualSector C H) o = none) :
    recordAt (subgroup C K) (residualSector C K)
        ((sourceOrbitEquiv C hblocks htarget) o) = none := by
  rw [sourceOrbitEquiv_recordAt C hblocks htarget o]
  exact ho

end SymmetricSubgroupAsymptotics.BinaryS16SourceOrbitRecordStatus

end
