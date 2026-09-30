import SymmetricSubgroupAsymptotics.BinaryS16CanonicalMixedBlockTable

/-!
# Recovering recorded S16 source blocks from the canonical mixed table

The mixed table stores a labelled representative chart for every positive
degree-eight and degree-sixteen source orbit.  This file records the semantic
fact needed by the chart-varying decoder: the range of that chart is exactly
the original labelled source orbit.  Consequently equality of two canonical
S16 tables matches every recorded orbit on one side with a unique recorded
orbit on the other side having the same literal ambient point set.

Only the source blocks represented in the mixed table are treated here.  The
recovery of omitted identity-route blocks from the common transported target
is deliberately left to the subsequent decoder module.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16RecordedBlockRecovery

open SymmetricSubgroupAsymptotics
open BinaryCarrierS16TaggedPositiveRoutes
open BinaryDegreeEightPhysicalDecoration
open BinaryDegreeEightSixteenPhysicalDecoration
open BinaryS16CanonicalCarrierProfile
open BinaryS16CanonicalMixedBlockTable
open BinaryS16DirectCertifiedOrbitProfile

/-! ## A local orbit lemma for omitted one-cell routes -/

/-- Local form of `OrbitProfileFullOn.orbit_eq_block`: only transitivity of
the one cell under consideration is needed.  This is the exact form used for
unrecorded critical and cyclic-four S16 routes. -/
theorem orbit_eq_block_of_transitive
    {ι X : Type*} {Ω : ι → Type*} {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {e : OrbitProfilePoints Ω m ≃ X}
    {G : Subgroup (Equiv.Perm X)}
    (hG : OrbitProfileFullOn U e G)
    {i : ι} (htrans : ∀ x y : Ω i,
      ∃ u : U i, (u : Equiv.Perm (Ω i)) x = y)
    (j : Fin (m i)) (x : Ω i) :
    MulAction.orbit G (e ⟨i,j,x⟩) =
      Set.range (fun y : Ω i ↦ e ⟨i,j,y⟩) := by
  ext z
  constructor
  · rintro ⟨g,rfl⟩
    obtain ⟨u,hu⟩ := hG.maps g i j
    exact ⟨(u : Equiv.Perm (Ω i)) x,(hu x).symm⟩
  · rintro ⟨y,rfl⟩
    obtain ⟨u,hu⟩ := htrans x y
    obtain ⟨g,hg⟩ := hG.full i j u
    refine ⟨g,?_⟩
    change (g : Equiv.Perm X) (e ⟨i,j,x⟩) = _
    rw [hg,hu]

/-! ## The literal point set encoded by a mixed record -/

/-- Forget the order of the stored chart, but retain its literal ambient
labels.  Its domain is selected by the degree discriminator in the record. -/
def representedPointSet {N : ℕ} :
    MixedBlockRecord N → Set (Fin (2 * N))
  | .degree8 r => Set.range r.targetRepresentative
  | .degree16 r => Set.range r.targetRepresentative

/-- The eight representatives of a semantic changed block exhaust its
original labelled orbit. -/
theorem changedDegreeEight_representedPointSet
    {N : ℕ} {H : Subgroup (Equiv.Perm (Fin (2 * N)))}
    (B : ChangedBlock H) :
    representedPointSet (.degree8 B.toRecord) = B.orbit.1.orbit := by
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact B.representative_mem i
  · intro hx
    obtain ⟨i,hi⟩ := B.chart.surjective ⟨x,hx⟩
    exact ⟨i,congrArg Subtype.val hi⟩

/-- The sixteen representatives of a semantic changed block exhaust its
original labelled orbit. -/
theorem changedDegreeSixteen_representedPointSet
    {N : ℕ} {H : Subgroup (Equiv.Perm (Fin (2 * N)))}
    (B : ChangedDegree16Block H) :
    representedPointSet (.degree16 B.toRecord) = B.orbit.1.orbit := by
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact ChangedDegree16Block.representative_mem H B i
  · intro hx
    obtain ⟨i,hi⟩ := B.chart.surjective ⟨x,hx⟩
    exact ⟨i,congrArg Subtype.val hi⟩

/-! ## The record extracted from a retained S16 certificate -/

variable {N : ℕ}
variable (H : Subgroup (Equiv.Perm (Fin (2 * N))))
variable (hH : ResidualSector H)

abbrev Orbit := OrbitProfileFromOrbits.Orbit H

/-- The semantic degree-eight block constructed by the retained route has
the certificate's original literal orbit. -/
@[simp] theorem degreeEight_changedBlock_orbit
    {o : Orbit H}
    (W : BinaryDegreeEightNormalizerSaturatedDirect.OrbitWitness H)
    (hpoint : Quotient.mk'' W.point = o)
    (R : DegreeEightRoute W.action W.axis) :
    (R.changedBlock W hpoint).orbit.1 = o := by
  subst o
  rfl

/-- The semantic degree-sixteen block constructed by the retained route has
the certificate's original literal orbit. -/
@[simp] theorem degreeSixteen_changedBlock_orbit
    {o : Orbit H}
    (W : BinaryDegree16PhysicalAnalyticClosure.OrbitWitness H)
    (hpoint : Quotient.mk'' W.point = o)
    (R : DegreeSixteenRoute W.action W.axis) :
    (R.changedBlock W hpoint).orbit.1 = o := by
  subst o
  rfl

/-- In the degree-eight branch the concrete record written by
`recordOfCertificate` is exactly the record of the semantic changed block. -/
theorem recordOfCertificate_carrier8_eq_toRecord
    {o : Orbit H}
    (W : BinaryDegreeEightNormalizerSaturatedDirect.OrbitWitness H)
    (hpoint : Quotient.mk'' W.point = o)
    (R : DegreeEightRoute W.action W.axis) :
    recordOfCertificate H o (.carrier8 W hpoint R) =
      some (.degree8 (R.changedBlock W hpoint).toRecord) := by
  subst o
  rfl

/-- In the degree-sixteen branch the concrete record written by
`recordOfCertificate` is exactly the record of the semantic changed block. -/
theorem recordOfCertificate_carrier16_eq_toRecord
    {o : Orbit H}
    (W : BinaryDegree16PhysicalAnalyticClosure.OrbitWitness H)
    (hpoint : Quotient.mk'' W.point = o)
    (R : DegreeSixteenRoute W.action W.axis) :
    recordOfCertificate H o (.carrier16 W hpoint R) =
      some (.degree16 (R.changedBlock W hpoint).toRecord) := by
  subst o
  rfl

/-- Whenever a retained certificate emits a mixed record, the point set in
that record is exactly the certificate's original source orbit. -/
theorem representedPointSet_of_recordOfCertificate_eq_some
    {o : Orbit H} (C : OrbitCertificate H o) {r : MixedBlockRecord N}
    (hr : recordOfCertificate H o C = some r) :
    representedPointSet r = o.orbit := by
  cases C with
  | c2 e he => simp [recordOfCertificate] at hr
  | v4 e he => simp [recordOfCertificate] at hr
  | d8 e he => simp [recordOfCertificate] at hr
  | e8 e he => simp [recordOfCertificate] at hr
  | cyclicFour W hpoint R => simp [recordOfCertificate] at hr
  | carrier8 W hpoint R =>
      let B := R.changedBlock W hpoint
      have hrecord : r = .degree8 B.toRecord := by
        exact (Option.some.inj
          ((recordOfCertificate_carrier8_eq_toRecord H W hpoint R).symm.trans
            hr)).symm
      subst r
      calc
        representedPointSet (.degree8 B.toRecord) = B.orbit.1.orbit :=
          changedDegreeEight_representedPointSet B
        _ = o.orbit := by
          rw [show B.orbit.1 = o by
            simpa [B] using degreeEight_changedBlock_orbit H W hpoint R]
  | carrier16 W hpoint R =>
      let B := R.changedBlock W hpoint
      have hrecord : r = .degree16 B.toRecord := by
        exact (Option.some.inj
          ((recordOfCertificate_carrier16_eq_toRecord H W hpoint R).symm.trans
            hr)).symm
      subst r
      calc
        representedPointSet (.degree16 B.toRecord) = B.orbit.1.orbit :=
          changedDegreeSixteen_representedPointSet B
        _ = o.orbit := by
          rw [show B.orbit.1 = o by
            simpa [B] using degreeSixteen_changedBlock_orbit H W hpoint R]

/-- The optional record at a literal orbit, when present, contains precisely
that orbit's ambient point set. -/
theorem representedPointSet_of_recordAt_eq_some
    {o : Orbit H} {r : MixedBlockRecord N}
    (hr : recordAt H hH o = some r) :
    representedPointSet r = o.orbit := by
  exact representedPointSet_of_recordOfCertificate_eq_some H
    (profile H hH o) hr

/-- The record extracted from a `RecordedOrbit` contains precisely that
orbit's ambient point set. -/
@[simp] theorem recordOf_representedPointSet
    (o : RecordedOrbit H hH) :
    representedPointSet (recordOf H hH o) = o.1.orbit := by
  exact representedPointSet_of_recordAt_eq_some H hH
    (Option.eq_some_of_isSome o.2)

/-! ## Matching recorded source blocks across equal canonical tables -/

/-- Least ambient points remain injective after restricting to the recorded
orbits. -/
theorem recordedOrbitLeast_injective :
    Function.Injective
      (fun o : RecordedOrbit H hH ↦ orbitLeast H o.1) := by
  intro o p hop
  exact Subtype.ext (orbitLeast_injective H hop)

/-- If the two record families give the same canonical table in one common
padding length, then every recorded orbit on the left has a unique recorded
orbit on the right with the same record and hence the same literal ambient
point set.  Using a common padding length avoids dependent elimination across
the two separately computed old-support sums. -/
theorem matching_recordedOrbit_of_table_eq
    {K : Subgroup (Equiv.Perm (Fin (2 * N)))}
    (hK : ResidualSector K)
    {Cold : ℕ}
    (hcountH : Fintype.card (RecordedOrbit H hH) ≤ Cold)
    (hcountK : Fintype.card (RecordedOrbit K hK) ≤ Cold)
    (htable :
      canonicalMixedBlockTableOfRecords
          (fun q : RecordedOrbit H hH ↦ orbitLeast H q.1)
          (recordedOrbitLeast_injective H hH)
          (recordOf H hH) (recordOf_leastPoint H hH) hcountH =
        canonicalMixedBlockTableOfRecords
          (fun q : RecordedOrbit K hK ↦ orbitLeast K q.1)
          (recordedOrbitLeast_injective K hK)
          (recordOf K hK) (recordOf_leastPoint K hK) hcountK)
    (o : RecordedOrbit H hH) :
    ∃! p : RecordedOrbit K hK,
      orbitLeast K p.1 = orbitLeast H o.1 ∧
        recordOf K hK p = recordOf H hH o ∧
        p.1.orbit = o.1.orbit := by
  have hmatch := canonicalMixedBlockTableOfRecords_matching_record
    (fun q : RecordedOrbit H hH ↦ orbitLeast H q.1)
    (recordedOrbitLeast_injective H hH)
    (recordOf H hH)
    (recordOf_leastPoint H hH)
    hcountH
    (fun q : RecordedOrbit K hK ↦ orbitLeast K q.1)
    (recordedOrbitLeast_injective K hK)
    (recordOf K hK)
    (recordOf_leastPoint K hK)
    hcountK
    htable
    o
  obtain ⟨p,⟨hkey,hrecord⟩,hunique⟩ := hmatch
  have horbit : p.1.orbit = o.1.orbit := by
    calc
      p.1.orbit = representedPointSet (recordOf K hK p) :=
        (recordOf_representedPointSet K hK p).symm
      _ = representedPointSet (recordOf H hH o) :=
        congrArg representedPointSet hrecord
      _ = o.1.orbit := recordOf_representedPointSet H hH o
  refine ⟨p,⟨hkey,hrecord,horbit⟩,?_⟩
  intro p' hp'
  exact hunique p' ⟨hp'.1,hp'.2.1⟩

end SymmetricSubgroupAsymptotics.BinaryS16RecordedBlockRecovery

end
