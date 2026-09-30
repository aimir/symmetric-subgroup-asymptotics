import SymmetricSubgroupAsymptotics.BinaryCarrierS16TaggedPositiveRoutes
import SymmetricSubgroupAsymptotics.BinaryS16JointOrbitData
import SymmetricSubgroupAsymptotics.BinaryS16RecordedBlockRecovery

/-!
# The source action retained by an S16 positive-block record

The point representatives in a positive mixed record are not merely an
enumeration of the underlying source block.  Together with the finite route
tag they are a chart for one fixed source action on `Fin 8` or `Fin 16`.
This file removes the hidden registry conjugator (and, in the exceptional
degree-eight branches, the hidden registry index) from that statement.

Consequently equality of positive records aligns both ingredients needed by
the local decoder: the fixed source action and its pointwise placement on the
original ambient labels.  Normal-axis and cross-orbit correlation recovery
remain separate carrier-transport statements.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.BinaryS16RecordedSourceAction

open SymmetricSubgroupAsymptotics
open BinaryActionRegistry8
open BinaryCarrierS16TaggedPositiveRoutes
open BinaryDegreeEightBaseRoutes
open BinaryDegreeEightPhysicalDecoration
open BinaryDegreeEightSixteenPhysicalDecoration
open BinaryS16CanonicalCarrierProfile
open BinaryS16DirectCertifiedOrbitProfile
open BinaryS16JointOrbitData
open BinaryS16CanonicalMixedBlockTable
open BinaryS16RecordedBlockRecovery

/-! ## Degree eight -/

/-- The canonical source action named by a degree-eight route tag.  In an
exceptional branch the checked transport chart itself determines the hidden
registry index, which is why the three-valued tag suffices. -/
def degreeEightSourceAction : LocalRouteTag →
    Subgroup (Equiv.Perm (Fin 8))
  | .base b => actions (baseIndex b)
  | .exceptional e =>
      (SymmetricSubgroupAsymptotics.binaryEightTransportChart e).source

/-- After the route's retained source placement is applied, the action named
by the finite tag is exactly the witness action.  This eliminates both the
hidden conjugator `g` and the hidden exceptional registry index `i`. -/
theorem degreeEightRoute_sourceAction
    {U : Subgroup (Equiv.Perm (Fin 8))}
    {M : Subgroup U} [M.Normal]
    (R : DegreeEightRoute U M) :
    relabelSubgroup R.sourcePointEquiv (degreeEightSourceAction R.tag) = U := by
  cases R with
  | base b hb t kind g hg =>
      change relabelSubgroup g.symm (actions (baseIndex b)) = U
      change relabelSubgroup g U = actions (baseIndex b) at hg
      rw [← hg]
      exact relabelSubgroup_symm g U
  | t16 i g hg source axis =>
      change relabelSubgroup g.symm
        (SymmetricSubgroupAsymptotics.binaryEightTransportChart 0).source = U
      change relabelSubgroup g U = actions i at hg
      rw [source, ← hg]
      exact relabelSubgroup_symm g U
  | t20 i g hg source axis =>
      change relabelSubgroup g.symm
        (SymmetricSubgroupAsymptotics.binaryEightTransportChart 1).source = U
      change relabelSubgroup g U = actions i at hg
      rw [source, ← hg]
      exact relabelSubgroup_symm g U
  | t21 i g hg source axis =>
      change relabelSubgroup g.symm
        (SymmetricSubgroupAsymptotics.binaryEightTransportChart 2).source = U
      change relabelSubgroup g U = actions i at hg
      rw [source, ← hg]
      exact relabelSubgroup_symm g U

/-- The chart stored by a degree-eight positive record realizes the
tag-determined source action as the literal restriction image on that source
orbit. -/
theorem degreeEightChangedBlock_sourceAction
    {N : ℕ} {H : Subgroup (Equiv.Perm (Fin (2 * N)))}
    {o : OrbitProfileFromOrbits.Orbit H}
    (W : BinaryDegreeEightNormalizerSaturatedDirect.OrbitWitness H)
    (hpoint : Quotient.mk'' W.point = o)
    (R : DegreeEightRoute W.action W.axis) :
    let B := R.changedBlock W hpoint
    relabelSubgroup B.chart (degreeEightSourceAction B.toRecord.route) =
      OrbitProfileFromOrbits.orbitImage H B.orbit.1 := by
  subst o
  change relabelSubgroup
      (R.sourcePointEquiv.trans
        (FusionActualOrbitCharts.orbitEquiv H W.point W.orbit_card))
      (degreeEightSourceAction R.tag) =
    OrbitProfileFromOrbits.orbitImage H (Quotient.mk'' W.point)
  rw [← relabelSubgroup_trans, degreeEightRoute_sourceAction]
  exact witnessEight_image_eq H W

/-! ## Degree sixteen -/

/-- The canonical source action named by a degree-sixteen route tag. -/
def degreeSixteenSourceAction : Degree16RouteTag →
    Subgroup (Equiv.Perm (Fin 16))
  | .t1086 => BinaryPairBinding16T1086.Original
  | .t1332 => BinarySelectedCatalogue16T1332.Original

/-- The retained source placement sends the action named by the two-valued
degree-sixteen tag to the actual witness action. -/
theorem degreeSixteenRoute_sourceAction
    {U : Subgroup (Equiv.Perm (Fin 16))}
    {M : Subgroup U} [M.Normal]
    (R : DegreeSixteenRoute U M) :
    relabelSubgroup R.sourcePointEquiv
      (degreeSixteenSourceAction R.tag) = U := by
  cases R with
  | t1086 g hg owner physical =>
      change relabelSubgroup g.symm BinaryPairBinding16T1086.Original = U
      change relabelSubgroup g U = BinaryPairBinding16T1086.Original at hg
      rw [← hg]
      exact relabelSubgroup_symm g U
  | t1332 g hg row physical =>
      change relabelSubgroup g.symm BinarySelectedCatalogue16T1332.Original = U
      change relabelSubgroup g U = BinarySelectedCatalogue16T1332.Original at hg
      rw [← hg]
      exact relabelSubgroup_symm g U

/-- The chart stored by a degree-sixteen positive record realizes the action
named by its route tag as the literal restriction image on the whole source
orbit.  In particular the four-cell `16T1086` carrier does not lose the
sixteen-point source action. -/
theorem degreeSixteenChangedBlock_sourceAction
    {N : ℕ} {H : Subgroup (Equiv.Perm (Fin (2 * N)))}
    {o : OrbitProfileFromOrbits.Orbit H}
    (W : BinaryDegree16PhysicalAnalyticClosure.OrbitWitness H)
    (hpoint : Quotient.mk'' W.point = o)
    (R : DegreeSixteenRoute W.action W.axis) :
    let B := R.changedBlock W hpoint
    relabelSubgroup B.chart (degreeSixteenSourceAction B.toRecord.route) =
      OrbitProfileFromOrbits.orbitImage H B.orbit.1 := by
  subst o
  change relabelSubgroup
      (R.sourcePointEquiv.trans
        (FusionActualOrbitCharts.orbitEquiv H W.point W.orbit_card))
      (degreeSixteenSourceAction R.tag) =
    OrbitProfileFromOrbits.orbitImage H (Quotient.mk'' W.point)
  rw [← relabelSubgroup_trans, degreeSixteenRoute_sourceAction]
  exact witnessSixteen_image_eq H W

/-! ## What literal record equality retains -/

/-- Equality of degree-eight records gives equality of the canonical source
actions named by their tags. -/
theorem degreeEightSourceAction_eq_of_record_eq
    {N : ℕ}
    {H K : Subgroup (Equiv.Perm (Fin (2 * N)))}
    {B : ChangedBlock H} {D : ChangedBlock K}
    (h : B.toRecord = D.toRecord) :
    degreeEightSourceAction B.toRecord.route =
      degreeEightSourceAction D.toRecord.route :=
  congrArg (fun r : BlockRecord N => degreeEightSourceAction r.route) h

/-- Equality of degree-eight records gives pointwise equality of the stored
source-action placements on the original ambient labels. -/
theorem degreeEightRepresentative_eq_of_record_eq
    {N : ℕ}
    {H K : Subgroup (Equiv.Perm (Fin (2 * N)))}
    {B : ChangedBlock H} {D : ChangedBlock K}
    (h : B.toRecord = D.toRecord) (i : Fin 8) :
    (B.chart i).1 = (D.chart i).1 := by
  exact congrFun
    (congrArg (fun r : BlockRecord N => r.targetRepresentative) h) i

/-- Equality of degree-sixteen records gives equality of the canonical
source actions named by their tags. -/
theorem degreeSixteenSourceAction_eq_of_record_eq
    {N : ℕ}
    {H K : Subgroup (Equiv.Perm (Fin (2 * N)))}
    {B : ChangedDegree16Block H} {D : ChangedDegree16Block K}
    (h : B.toRecord = D.toRecord) :
    degreeSixteenSourceAction B.toRecord.route =
      degreeSixteenSourceAction D.toRecord.route :=
  congrArg (fun r : Degree16BlockRecord N =>
    degreeSixteenSourceAction r.route) h

/-- Equality of degree-sixteen records gives pointwise equality of the
stored source-action placements on the original ambient labels. -/
theorem degreeSixteenRepresentative_eq_of_record_eq
    {N : ℕ}
    {H K : Subgroup (Equiv.Perm (Fin (2 * N)))}
    {B : ChangedDegree16Block H} {D : ChangedDegree16Block K}
    (h : B.toRecord = D.toRecord) (i : Fin 16) :
    (B.chart i).1 = (D.chart i).1 := by
  exact congrFun
    (congrArg (fun r : Degree16BlockRecord N => r.targetRepresentative) h) i

/-! ## Literal restriction images of matched positive records -/

/-- Two semantic degree-eight blocks carrying the action asserted by their
records have identical literal restriction images after the equality of
their represented point sets is removed. -/
theorem degreeEightOrbitImage_eq_of_record_eq
    {N : ℕ}
    {H K : Subgroup (Equiv.Perm (Fin (2 * N)))}
    (B : ChangedBlock H) (D : ChangedBlock K)
    (hB : relabelSubgroup B.chart
        (degreeEightSourceAction B.toRecord.route) =
      OrbitProfileFromOrbits.orbitImage H B.orbit.1)
    (hD : relabelSubgroup D.chart
        (degreeEightSourceAction D.toRecord.route) =
      OrbitProfileFromOrbits.orbitImage K D.orbit.1)
    (hrecord : B.toRecord = D.toRecord)
    (horbit : D.orbit.1.orbit = B.orbit.1.orbit) :
    relabelSubgroup (Equiv.setCongr horbit.symm)
        (OrbitProfileFromOrbits.orbitImage H B.orbit.1) =
      OrbitProfileFromOrbits.orbitImage K D.orbit.1 := by
  have haction : degreeEightSourceAction B.toRecord.route =
      degreeEightSourceAction D.toRecord.route :=
    degreeEightSourceAction_eq_of_record_eq hrecord
  have hchart : B.chart.trans (Equiv.setCongr horbit.symm) = D.chart := by
    apply Equiv.ext
    intro i
    apply Subtype.ext
    exact degreeEightRepresentative_eq_of_record_eq hrecord i
  calc
    relabelSubgroup (Equiv.setCongr horbit.symm)
        (OrbitProfileFromOrbits.orbitImage H B.orbit.1) =
        relabelSubgroup (Equiv.setCongr horbit.symm)
          (relabelSubgroup B.chart
            (degreeEightSourceAction B.toRecord.route)) :=
      congrArg (relabelSubgroup (Equiv.setCongr horbit.symm)) hB.symm
    _ = relabelSubgroup (B.chart.trans (Equiv.setCongr horbit.symm))
          (degreeEightSourceAction B.toRecord.route) :=
      relabelSubgroup_trans B.chart (Equiv.setCongr horbit.symm) _
    _ = relabelSubgroup D.chart
          (degreeEightSourceAction D.toRecord.route) := by
      rw [hchart,haction]
    _ = OrbitProfileFromOrbits.orbitImage K D.orbit.1 := hD

/-- Degree-sixteen analogue of `degreeEightOrbitImage_eq_of_record_eq`.
The proof does not inspect the carrier, so it applies unchanged to the
nonabelian proper-subdirect `16T1086` route. -/
theorem degreeSixteenOrbitImage_eq_of_record_eq
    {N : ℕ}
    {H K : Subgroup (Equiv.Perm (Fin (2 * N)))}
    (B : ChangedDegree16Block H) (D : ChangedDegree16Block K)
    (hB : relabelSubgroup B.chart
        (degreeSixteenSourceAction B.toRecord.route) =
      OrbitProfileFromOrbits.orbitImage H B.orbit.1)
    (hD : relabelSubgroup D.chart
        (degreeSixteenSourceAction D.toRecord.route) =
      OrbitProfileFromOrbits.orbitImage K D.orbit.1)
    (hrecord : B.toRecord = D.toRecord)
    (horbit : D.orbit.1.orbit = B.orbit.1.orbit) :
    relabelSubgroup (Equiv.setCongr horbit.symm)
        (OrbitProfileFromOrbits.orbitImage H B.orbit.1) =
      OrbitProfileFromOrbits.orbitImage K D.orbit.1 := by
  have haction : degreeSixteenSourceAction B.toRecord.route =
      degreeSixteenSourceAction D.toRecord.route :=
    degreeSixteenSourceAction_eq_of_record_eq hrecord
  have hchart : B.chart.trans (Equiv.setCongr horbit.symm) = D.chart := by
    apply Equiv.ext
    intro i
    apply Subtype.ext
    exact degreeSixteenRepresentative_eq_of_record_eq hrecord i
  calc
    relabelSubgroup (Equiv.setCongr horbit.symm)
        (OrbitProfileFromOrbits.orbitImage H B.orbit.1) =
        relabelSubgroup (Equiv.setCongr horbit.symm)
          (relabelSubgroup B.chart
            (degreeSixteenSourceAction B.toRecord.route)) :=
      congrArg (relabelSubgroup (Equiv.setCongr horbit.symm)) hB.symm
    _ = relabelSubgroup (B.chart.trans (Equiv.setCongr horbit.symm))
          (degreeSixteenSourceAction B.toRecord.route) :=
      relabelSubgroup_trans B.chart (Equiv.setCongr horbit.symm) _
    _ = relabelSubgroup D.chart
          (degreeSixteenSourceAction D.toRecord.route) := by
      rw [hchart,haction]
    _ = OrbitProfileFromOrbits.orbitImage K D.orbit.1 := hD

/-- Two positive certificates writing the same mixed record have conjugate
literal source-orbit images, with the conjugacy being only the proof cast
between their equal original-labelled point sets. -/
theorem orbitImage_eq_of_positive_certificate_records
    {N : ℕ}
    {H K : Subgroup (Equiv.Perm (Fin (2 * N)))}
    {o : OrbitProfileFromOrbits.Orbit H}
    {p : OrbitProfileFromOrbits.Orbit K}
    (CO : OrbitCertificate H o) (CP : OrbitCertificate K p)
    {r : MixedBlockRecord N}
    (hO : recordOfCertificate H o CO = some r)
    (hP : recordOfCertificate K p CP = some r)
    (horbit : p.orbit = o.orbit) :
    relabelSubgroup (Equiv.setCongr horbit.symm)
        (OrbitProfileFromOrbits.orbitImage H o) =
      OrbitProfileFromOrbits.orbitImage K p := by
  cases CO with
  | c2 e he => simp [recordOfCertificate] at hO
  | v4 e he => simp [recordOfCertificate] at hO
  | d8 e he => simp [recordOfCertificate] at hO
  | e8 e he => simp [recordOfCertificate] at hO
  | cyclicFour W hpoint R => simp [recordOfCertificate] at hO
  | carrier8 W hpoint R =>
      cases CP with
      | c2 e he => simp [recordOfCertificate] at hP
      | v4 e he => simp [recordOfCertificate] at hP
      | d8 e he => simp [recordOfCertificate] at hP
      | e8 e he => simp [recordOfCertificate] at hP
      | cyclicFour W' hpoint' R' => simp [recordOfCertificate] at hP
      | carrier8 W' hpoint' R' =>
          subst o
          subst p
          let B := R.changedBlock W rfl
          let D := R'.changedBlock W' rfl
          have hmixed : MixedBlockRecord.degree8 B.toRecord =
              MixedBlockRecord.degree8 D.toRecord := by
            apply Option.some.inj
            exact (recordOfCertificate_carrier8_eq_toRecord H W rfl R).symm.trans
              (hO.trans (hP.symm.trans
                (recordOfCertificate_carrier8_eq_toRecord K W' rfl R')))
          have hrecord : B.toRecord = D.toRecord :=
            MixedBlockRecord.degree8.inj hmixed
          apply degreeEightOrbitImage_eq_of_record_eq B D
          · simpa [B] using degreeEightChangedBlock_sourceAction W rfl R
          · simpa [D] using degreeEightChangedBlock_sourceAction W' rfl R'
          · exact hrecord
          · simpa [B,D] using horbit
      | carrier16 W' hpoint' R' =>
          have hmixed : MixedBlockRecord.degree8
                (R.changedBlock W hpoint).toRecord =
              MixedBlockRecord.degree16
                (R'.changedBlock W' hpoint').toRecord := by
            apply Option.some.inj
            exact (recordOfCertificate_carrier8_eq_toRecord H W hpoint R).symm.trans
              (hO.trans (hP.symm.trans
                (recordOfCertificate_carrier16_eq_toRecord K W' hpoint' R')))
          cases hmixed
  | carrier16 W hpoint R =>
      cases CP with
      | c2 e he => simp [recordOfCertificate] at hP
      | v4 e he => simp [recordOfCertificate] at hP
      | d8 e he => simp [recordOfCertificate] at hP
      | e8 e he => simp [recordOfCertificate] at hP
      | cyclicFour W' hpoint' R' => simp [recordOfCertificate] at hP
      | carrier8 W' hpoint' R' =>
          have hmixed : MixedBlockRecord.degree16
                (R.changedBlock W hpoint).toRecord =
              MixedBlockRecord.degree8
                (R'.changedBlock W' hpoint').toRecord := by
            apply Option.some.inj
            exact (recordOfCertificate_carrier16_eq_toRecord H W hpoint R).symm.trans
              (hO.trans (hP.symm.trans
                (recordOfCertificate_carrier8_eq_toRecord K W' hpoint' R')))
          cases hmixed
      | carrier16 W' hpoint' R' =>
          subst o
          subst p
          let B := R.changedBlock W rfl
          let D := R'.changedBlock W' rfl
          have hmixed : MixedBlockRecord.degree16 B.toRecord =
              MixedBlockRecord.degree16 D.toRecord := by
            apply Option.some.inj
            exact (recordOfCertificate_carrier16_eq_toRecord H W rfl R).symm.trans
              (hO.trans (hP.symm.trans
                (recordOfCertificate_carrier16_eq_toRecord K W' rfl R')))
          have hrecord : B.toRecord = D.toRecord :=
            MixedBlockRecord.degree16.inj hmixed
          apply degreeSixteenOrbitImage_eq_of_record_eq B D
          · simpa [B] using degreeSixteenChangedBlock_sourceAction W rfl R
          · simpa [D] using degreeSixteenChangedBlock_sourceAction W' rfl R'
          · exact hrecord
          · simpa [B,D] using horbit

/-- Public recorded-orbit form used after canonical-table matching.  Equality
of the retained record and of the literal point set already aligns the full
source restriction images; no target-subgroup hypothesis is needed here. -/
theorem recordedOrbit_orbitImage_eq
    {N : ℕ}
    {H K : Subgroup (Equiv.Perm (Fin (2 * N)))}
    (hH : ResidualSector H) (hK : ResidualSector K)
    (o : RecordedOrbit H hH) (p : RecordedOrbit K hK)
    (hrecord : recordOf K hK p = recordOf H hH o)
    (horbit : p.1.orbit = o.1.orbit) :
    relabelSubgroup (Equiv.setCongr horbit.symm)
        (OrbitProfileFromOrbits.orbitImage H o.1) =
      OrbitProfileFromOrbits.orbitImage K p.1 := by
  apply orbitImage_eq_of_positive_certificate_records
      (profile H hH o.1) (profile K hK p.1)
  · exact Option.eq_some_of_isSome o.2
  · change recordAt K hK p.1 = some (recordOf H hH o)
    calc
      recordAt K hK p.1 = some (recordOf K hK p) :=
        Option.eq_some_of_isSome p.2
      _ = some (recordOf H hH o) := congrArg some hrecord
  · exact horbit

end SymmetricSubgroupAsymptotics.BinaryS16RecordedSourceAction

end
