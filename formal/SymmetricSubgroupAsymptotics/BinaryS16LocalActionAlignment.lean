import SymmetricSubgroupAsymptotics.BinaryS16RecordedSourceAction
import SymmetricSubgroupAsymptotics.BinaryS16SourceOrbitReindex
import SymmetricSubgroupAsymptotics.BinaryS16SourceOrbitRecordStatus
import SymmetricSubgroupAsymptotics.BinaryS16UnrecordedOrbitImageRecovery

/-!
# Alignment of every matched S16 local source action

Equality of the mixed table and physical target first identifies the literal
source-orbit partition.  On a recorded orbit, equality of the retained record
identifies the complete source restriction image.  On an unrecorded orbit,
the one-cell theorem identifies that restriction image with the restriction
of the common physical target.  Hence every pair of matched source orbits has
conjugate complete local actions.

The final theorem expresses this conjugacy in the exact local point
equivalence already used by `BinaryS16SourceOrbitReindex`.  It is the local
input needed to transport the complete correlated flat source, rather than
only its orbit partition.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16LocalActionAlignment

open SymmetricSubgroupAsymptotics
open BinaryS16CanonicalMixedBlockTable
open BinaryS16DirectPhysicalEncoding
open BinaryS16DirectPhysicalTarget
open BinaryS16JointOrbitData
open BinaryS16RecordedSourceAction
open BinaryS16SourceOrbitPartition
open BinaryS16SourceOrbitRecordStatus
open BinaryS16SourceOrbitReindex
open BinaryS16UnrecordedOrbitImageRecovery

variable {N : ℕ} (C : BinaryS16DirectFixedSupportClosure.SupportIndex N)

abbrev Actual := BinaryS16DirectPhysicalTarget.Actual C

/-- Equality of the retained mixed record aligns the complete restriction
images on a matched recorded orbit. -/
theorem matched_recordedOrbitImage
    {A B : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C A =
      BinaryS16DirectPhysicalEncoding.blocks C B)
    (htarget : targetSubgroup C A = targetSubgroup C B)
    (o : OrbitProfileFromOrbits.Orbit (subgroup C A))
    (ho : (recordAt (subgroup C A) (residualSector C A) o).isSome) :
    relabelSubgroup
        (Equiv.setCongr (sourceOrbitEquiv_orbit C hblocks htarget o))
        (OrbitProfileFromOrbits.orbitImage (subgroup C B)
          ((sourceOrbitEquiv C hblocks htarget) o)) =
      OrbitProfileFromOrbits.orbitImage (subgroup C A) o := by
  obtain ⟨hp,hrecord⟩ := sourceOrbitEquiv_recorded C
    hblocks htarget o ho
  let pA : RecordedOrbit (subgroup C A) (residualSector C A) := ⟨o,ho⟩
  let pB : RecordedOrbit (subgroup C B) (residualSector C B) :=
    ⟨(sourceOrbitEquiv C hblocks htarget) o,hp⟩
  simpa only [pA,pB] using
    (recordedOrbit_orbitImage_eq
      (residualSector C B) (residualSector C A) pB pA
      hrecord.symm (sourceOrbitEquiv_orbit C hblocks htarget o).symm)

/-- Two target orbits with the same literal point set give the same target
restriction image after transport to that common set. -/
private theorem targetOrbitImages_eq
    {G : Subgroup (Equiv.Perm (Fin (2 * N)))}
    {o p : Set (Fin (2 * N))}
    {q r : OrbitProfileFromOrbits.Orbit G}
    (hq : q.orbit = o) (hr : r.orbit = p) (hpo : p = o) :
    relabelSubgroup (Equiv.setCongr hpo)
        (relabelSubgroup (Equiv.setCongr hr)
          (OrbitProfileFromOrbits.orbitImage G r)) =
      relabelSubgroup (Equiv.setCongr hq)
        (OrbitProfileFromOrbits.orbitImage G q) := by
  have hqr : r = q :=
    MulAction.orbitRel.Quotient.orbit_injective
      (hr.trans (hpo.trans hq.symm))
  subst r
  have he : (Equiv.setCongr hr).trans (Equiv.setCongr hpo) =
      Equiv.setCongr hq := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    rfl
  rw [relabelSubgroup_trans,he]

/-- Transport a complete target-orbit image across equality of the ambient
target subgroup.  Packaging the dependent orbit and its chart together
avoids rewriting through quotient types. -/
private theorem cast_targetOrbitImage
    {G K L : Subgroup (Equiv.Perm (Fin (2 * N)))}
    (hGK : G = K)
    (p : OrbitProfileFromOrbits.Orbit L)
    (r : OrbitProfileFromOrbits.Orbit K)
    (hr : r.orbit = p.orbit)
    (himage : relabelSubgroup (Equiv.setCongr hr)
        (OrbitProfileFromOrbits.orbitImage K r) =
      OrbitProfileFromOrbits.orbitImage L p) :
    ∃ r' : OrbitProfileFromOrbits.Orbit G,
      ∃ hr' : r'.orbit = p.orbit,
        relabelSubgroup (Equiv.setCongr hr')
            (OrbitProfileFromOrbits.orbitImage G r') =
          OrbitProfileFromOrbits.orbitImage L p := by
  cases hGK
  exact ⟨r,hr,himage⟩

/-- Replace an orbit index by an equal quotient-orbit value while retaining
the chosen literal point-set equality used for conjugation. -/
private theorem orbitImage_transport_index
    {G L : Subgroup (Equiv.Perm (Fin (2 * N)))}
    {p r : OrbitProfileFromOrbits.Orbit G}
    {o : OrbitProfileFromOrbits.Orbit L}
    (hpr : p = r) (hpo : p.orbit = o.orbit)
    (hro : r.orbit = o.orbit)
    (himage : relabelSubgroup (Equiv.setCongr hpo)
        (OrbitProfileFromOrbits.orbitImage G p) =
      OrbitProfileFromOrbits.orbitImage L o) :
    relabelSubgroup (Equiv.setCongr hro)
        (OrbitProfileFromOrbits.orbitImage G r) =
      OrbitProfileFromOrbits.orbitImage L o := by
  subst r
  simpa only using himage

/-- The complete source restriction images on matched unrecorded orbits are
conjugate through their literal equality of ambient point sets. -/
theorem matched_unrecordedOrbitImage
    {A B : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C A =
      BinaryS16DirectPhysicalEncoding.blocks C B)
    (htarget : targetSubgroup C A = targetSubgroup C B)
    (o : OrbitProfileFromOrbits.Orbit (subgroup C A))
    (ho : recordAt (subgroup C A) (residualSector C A) o = none) :
    relabelSubgroup
        (Equiv.setCongr (sourceOrbitEquiv_orbit C hblocks htarget o))
        (OrbitProfileFromOrbits.orbitImage (subgroup C B)
          ((sourceOrbitEquiv C hblocks htarget) o)) =
      OrbitProfileFromOrbits.orbitImage (subgroup C A) o := by
  let p := (sourceOrbitEquiv C hblocks htarget) o
  have hp : recordAt (subgroup C B) (residualSector C B) p = none :=
    sourceOrbitEquiv_unrecorded C hblocks htarget o ho
  obtain ⟨q,hq,himageA⟩ :=
    unrecorded_sourceOrbitImage_is_targetOrbitImage C A o ho
  obtain ⟨r,hr,himageB⟩ :=
    unrecorded_sourceOrbitImage_is_targetOrbitImage C B p hp
  obtain ⟨rA,hrA,himageBA⟩ := cast_targetOrbitImage
    htarget p r hr himageB
  calc
    relabelSubgroup
        (Equiv.setCongr (sourceOrbitEquiv_orbit C hblocks htarget o))
        (OrbitProfileFromOrbits.orbitImage (subgroup C B) p) =
        relabelSubgroup
          (Equiv.setCongr (sourceOrbitEquiv_orbit C hblocks htarget o))
          (relabelSubgroup (Equiv.setCongr hrA)
            (OrbitProfileFromOrbits.orbitImage (targetSubgroup C A) rA)) := by
          rw [himageBA]
    _ = relabelSubgroup (Equiv.setCongr hq)
          (OrbitProfileFromOrbits.orbitImage (targetSubgroup C A) q) :=
      targetOrbitImages_eq hq hrA
        (sourceOrbitEquiv_orbit C hblocks htarget o)
    _ = OrbitProfileFromOrbits.orbitImage (subgroup C A) o := himageA

/-- Uniform action-image alignment on every matched source orbit. -/
theorem matched_sourceOrbitImage
    {A B : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C A =
      BinaryS16DirectPhysicalEncoding.blocks C B)
    (htarget : targetSubgroup C A = targetSubgroup C B)
    (o : OrbitProfileFromOrbits.Orbit (subgroup C A)) :
    relabelSubgroup
        (Equiv.setCongr (sourceOrbitEquiv_orbit C hblocks htarget o))
        (OrbitProfileFromOrbits.orbitImage (subgroup C B)
          ((sourceOrbitEquiv C hblocks htarget) o)) =
      OrbitProfileFromOrbits.orbitImage (subgroup C A) o := by
  by_cases ho : (recordAt (subgroup C A) (residualSector C A) o).isSome
  · exact matched_recordedOrbitImage C hblocks htarget o ho
  · exact matched_unrecordedOrbitImage C hblocks htarget o
      (Option.not_isSome_iff_eq_none.mp ho)

/-- The exact local point equivalence used to reindex occurrences conjugates
the full local source action.  This statement includes all seven certificate
constructors and retains the complete action, not merely orbit size or point
set. -/
theorem occurrenceLocalPointEquiv_action
    {A B : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C A =
      BinaryS16DirectPhysicalEncoding.blocks C B)
    (htarget : targetSubgroup C A = targetSubgroup C B)
    (q : BinaryS16SourceOrbitReindex.Occurrence C A) :
    relabelSubgroup
        (occurrenceLocalPointEquiv C hblocks htarget q)
        (action (subgroup C A) (residualSector C A) q.1) =
      action (subgroup C B) (residualSector C B)
        (occurrenceEquiv C hblocks htarget q).1 := by
  let dataA := data (subgroup C A) (residualSector C A)
  let dataB := data (subgroup C B) (residualSector C B)
  let orbitE :
      (dataB.orbitIndex (occurrenceEquiv C hblocks htarget q)).orbit ≃
        (dataA.orbitIndex q).orbit :=
    Equiv.setCongr (occurrenceEquiv_orbit C hblocks htarget q)
  have himage := matched_sourceOrbitImage C hblocks htarget
    (dataA.orbitIndex q)
  have hindex :
      (sourceOrbitEquiv C hblocks htarget) (dataA.orbitIndex q) =
        dataB.orbitIndex (occurrenceEquiv C hblocks htarget q) := by
    exact (occurrenceEquiv_orbitIndex C hblocks htarget q).symm
  have himage' := orbitImage_transport_index hindex
    (sourceOrbitEquiv_orbit C hblocks htarget (dataA.orbitIndex q))
    (occurrenceEquiv_orbit C hblocks htarget q) himage
  have hinverse :
      relabelSubgroup orbitE.symm
          (OrbitProfileFromOrbits.orbitImage
            (subgroup C A) (dataA.orbitIndex q)) =
      OrbitProfileFromOrbits.orbitImage
          (subgroup C B)
          (dataB.orbitIndex (occurrenceEquiv C hblocks htarget q)) := by
    rw [← himage']
    exact relabelSubgroup_symm orbitE _
  change relabelSubgroup
      ((dataA.localChart q.1 q.2).trans
        ((Equiv.setCongr
          (occurrenceEquiv_orbit C hblocks htarget q).symm).trans
          (dataB.localChart
            (occurrenceEquiv C hblocks htarget q).1
            (occurrenceEquiv C hblocks htarget q).2).symm))
      (action (subgroup C A) (residualSector C A) q.1) = _
  have horbitEsymm :
      Equiv.setCongr (occurrenceEquiv_orbit C hblocks htarget q).symm =
        orbitE.symm := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    rfl
  calc
    relabelSubgroup
        ((dataA.localChart q.1 q.2).trans
          ((Equiv.setCongr
            (occurrenceEquiv_orbit C hblocks htarget q).symm).trans
            (dataB.localChart
              (occurrenceEquiv C hblocks htarget q).1
              (occurrenceEquiv C hblocks htarget q).2).symm))
        (action (subgroup C A) (residualSector C A) q.1) =
      relabelSubgroup
        ((Equiv.setCongr
          (occurrenceEquiv_orbit C hblocks htarget q).symm).trans
          (dataB.localChart
            (occurrenceEquiv C hblocks htarget q).1
            (occurrenceEquiv C hblocks htarget q).2).symm)
        (relabelSubgroup (dataA.localChart q.1 q.2)
          (action (subgroup C A) (residualSector C A) q.1)) :=
      (relabelSubgroup_trans _ _ _).symm
    _ = relabelSubgroup
        ((Equiv.setCongr
          (occurrenceEquiv_orbit C hblocks htarget q).symm).trans
          (dataB.localChart
            (occurrenceEquiv C hblocks htarget q).1
            (occurrenceEquiv C hblocks htarget q).2).symm)
        (OrbitProfileFromOrbits.orbitImage
          (subgroup C A) (dataA.orbitIndex q)) := by
      rw [dataA.localChart_image]
    _ = relabelSubgroup
        (dataB.localChart
          (occurrenceEquiv C hblocks htarget q).1
          (occurrenceEquiv C hblocks htarget q).2).symm
        (relabelSubgroup
          (Equiv.setCongr
            (occurrenceEquiv_orbit C hblocks htarget q).symm)
          (OrbitProfileFromOrbits.orbitImage
            (subgroup C A) (dataA.orbitIndex q))) :=
      (relabelSubgroup_trans _ _ _).symm
    _ = relabelSubgroup
        (dataB.localChart
          (occurrenceEquiv C hblocks htarget q).1
          (occurrenceEquiv C hblocks htarget q).2).symm
        (OrbitProfileFromOrbits.orbitImage (subgroup C B)
          (dataB.orbitIndex (occurrenceEquiv C hblocks htarget q))) := by
      rw [horbitEsymm,hinverse]
    _ = action (subgroup C B) (residualSector C B)
        (occurrenceEquiv C hblocks htarget q).1 := by
      rw [← dataB.localChart_image]
      exact relabelSubgroup_symm
          (dataB.localChart
            (occurrenceEquiv C hblocks htarget q).1
            (occurrenceEquiv C hblocks htarget q).2)
          (action (subgroup C B) (residualSector C B)
            (occurrenceEquiv C hblocks htarget q).1)

end SymmetricSubgroupAsymptotics.BinaryS16LocalActionAlignment

end
