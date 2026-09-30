import SymmetricSubgroupAsymptotics.BinaryS16FixedTableMatching
import SymmetricSubgroupAsymptotics.BinaryS16UnrecordedOrbitRecovery

/-!
# Recovering the complete source-orbit partition on an S16 key fibre

Equality of the retained mixed table matches the recorded source blocks.
For an omitted source block, the fusion-natural target realizes the whole
block as one target orbit.  If the corresponding block for the other source
were recorded, matching that recorded block back would produce a recorded
block of the first source meeting the omitted block, which is impossible.
Thus the other block is omitted too, and equality of target subgroups matches
the two literal blocks.

The result is an equivalence of the two source-orbit index types preserving
their actual subsets of the common ambient `Fin (2*N)` point set.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16SourceOrbitPartition

open SymmetricSubgroupAsymptotics
open BinaryS16CanonicalMixedBlockTable
open BinaryS16DirectFixedSupportClosure
open BinaryS16DirectPhysicalEncoding
open BinaryS16DirectPhysicalTarget
open BinaryS16FixedTableMatching
open BinaryS16UnrecordedOrbitRecovery

variable {N : ℕ} (C : SupportIndex N)

abbrev Actual := BinaryS16DirectPhysicalTarget.Actual C

/-- Equality of both concrete physical keys matches every literal source
orbit on the left with a unique literal source orbit on the right having the
same ambient point set.  The omitted-orbit case uses the target only after
excluding a recorded block on the other side. -/
theorem matching_sourceOrbit_of_keys_eq
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K)
    (o : OrbitProfileFromOrbits.Orbit (subgroup C H)) :
    ∃! p : OrbitProfileFromOrbits.Orbit (subgroup C K),
      p.orbit = o.orbit := by
  have hblocksTarget : BinaryS16DirectPhysicalTarget.blocks C H =
      BinaryS16DirectPhysicalTarget.blocks C K := by
    simpa only [BinaryS16DirectPhysicalEncoding.blocks,
      BinaryS16DirectPhysicalEncoding.rawBlocks,
      BinaryS16DirectPhysicalTarget.blocks] using hblocks
  by_cases hrecorded : (recordAt
      (subgroup C H) (residualSector C H) o).isSome
  · obtain ⟨p,hp,_hp_unique⟩ := matching_recordedOrbit_of_blocks_eq C hblocksTarget
      (⟨o,hrecorded⟩ : RecordedOrbit
        (subgroup C H) (residualSector C H))
    refine ⟨p.1,hp.2.2,?_⟩
    intro p' hp'
    exact MulAction.orbitRel.Quotient.orbit_injective
      (hp'.trans hp.2.2.symm)
  · have hunrecordedH : recordAt
        (subgroup C H) (residualSector C H) o = none :=
      Option.not_isSome_iff_eq_none.mp hrecorded
    obtain ⟨z,hzo⟩ := unrecorded_sourceOrbit_is_targetOrbit
      C H o hunrecordedH
    let p : OrbitProfileFromOrbits.Orbit (subgroup C K) := Quotient.mk'' z
    have hzp : z ∈ p.orbit := by
      change z ∈ MulAction.orbit (subgroup C K) z
      exact MulAction.mem_orbit_self z
    have hunrecordedK : recordAt
        (subgroup C K) (residualSector C K) p = none := by
      apply Option.not_isSome_iff_eq_none.mp
      intro hprecorded
      obtain ⟨q,hq,_hq_unique⟩ := matching_recordedOrbit_of_blocks_eq C hblocksTarget.symm
        (⟨p,hprecorded⟩ : RecordedOrbit
          (subgroup C K) (residualSector C K))
      have hzq : z ∈ q.1.orbit := by
        rw [hq.2.2]
        exact hzp
      have hzo' : z ∈ o.orbit := by
        rw [← hzo]
        exact MulAction.mem_orbit_self z
      have hqo : q.1 = o :=
        (MulAction.orbitRel.Quotient.mem_orbit.mp hzq).symm.trans
          (MulAction.orbitRel.Quotient.mem_orbit.mp hzo')
      exact hrecorded (hqo ▸ q.2)
    obtain ⟨w,hwp⟩ := unrecorded_sourceOrbit_is_targetOrbit
      C K p hunrecordedK
    have hzw : z ∈ MulAction.orbit (targetSubgroup C K) w := by
      rw [hwp]
      exact hzp
    have htargetOrbit :
        MulAction.orbit (targetSubgroup C K) z =
          MulAction.orbit (targetSubgroup C K) w :=
      MulAction.orbit_eq_iff.mpr hzw
    have hpo : p.orbit = o.orbit := by
      calc
        p.orbit = MulAction.orbit (targetSubgroup C K) w := hwp.symm
        _ = MulAction.orbit (targetSubgroup C K) z := htargetOrbit.symm
        _ = MulAction.orbit (targetSubgroup C H) z := by rw [htarget]
        _ = o.orbit := hzo
    refine ⟨p,hpo,?_⟩
    intro p' hp'
    exact MulAction.orbitRel.Quotient.orbit_injective
      (hp'.trans hpo.symm)

/-- The source orbit on the other side of the key fibre with the same literal
ambient block. -/
def matchedOrbit
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K)
    (o : OrbitProfileFromOrbits.Orbit (subgroup C H)) :
    OrbitProfileFromOrbits.Orbit (subgroup C K) :=
  Classical.choose (matching_sourceOrbit_of_keys_eq C hblocks htarget o)

@[simp] theorem matchedOrbit_orbit
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K)
    (o : OrbitProfileFromOrbits.Orbit (subgroup C H)) :
    (matchedOrbit C hblocks htarget o).orbit = o.orbit :=
  (Classical.choose_spec
    (matching_sourceOrbit_of_keys_eq C hblocks htarget o)).1

/-- Equal S16 physical keys canonically identify the complete source-orbit
partitions, with every equivalence class sent to the identical subset of the
original labelled ambient point set. -/
def sourceOrbitEquiv
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K) :
    OrbitProfileFromOrbits.Orbit (subgroup C H) ≃
      OrbitProfileFromOrbits.Orbit (subgroup C K) where
  toFun := matchedOrbit C hblocks htarget
  invFun := matchedOrbit C hblocks.symm htarget.symm
  left_inv o := by
    apply MulAction.orbitRel.Quotient.orbit_injective
    exact (matchedOrbit_orbit C hblocks.symm htarget.symm
      (matchedOrbit C hblocks htarget o)).trans
        (matchedOrbit_orbit C hblocks htarget o)
  right_inv p := by
    apply MulAction.orbitRel.Quotient.orbit_injective
    exact (matchedOrbit_orbit C hblocks htarget
      (matchedOrbit C hblocks.symm htarget.symm p)).trans
        (matchedOrbit_orbit C hblocks.symm htarget.symm p)

@[simp] theorem sourceOrbitEquiv_orbit
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K)
    (o : OrbitProfileFromOrbits.Orbit (subgroup C H)) :
    ((sourceOrbitEquiv C hblocks htarget) o).orbit = o.orbit :=
  matchedOrbit_orbit C hblocks htarget o

@[simp] theorem sourceOrbitEquiv_symm_orbit
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K)
    (p : OrbitProfileFromOrbits.Orbit (subgroup C K)) :
    ((sourceOrbitEquiv C hblocks htarget).symm p).orbit = p.orbit := by
  change (matchedOrbit C hblocks.symm htarget.symm p).orbit = p.orbit
  exact matchedOrbit_orbit C hblocks.symm htarget.symm p

end SymmetricSubgroupAsymptotics.BinaryS16SourceOrbitPartition

end
