import SymmetricSubgroupAsymptotics.BinaryS16JointOrbitData
import SymmetricSubgroupAsymptotics.BinaryCarrierCanonicalCertifiedSlotBridge
import SymmetricSubgroupAsymptotics.FusionOrbitQuotientAxisTransport

/-!
# Certified routing for the joint S16 orbit profile

This file turns the certificate retained by `BinaryS16JointOrbitData` into a
certified slot on each literal canonical coordinate axis.  The construction
uses no second orbit-profile choice.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.BinaryS16JointAxisRouting

open SymmetricSubgroupAsymptotics
open BinaryCarrierCanonicalOrbitPhysicalEncoding
open BinaryCarrierCanonicalCertifiedSlotBridge
open BinaryCarrierCertifiedRetention
open BinaryCarrierMenuSlots
open BinaryCarrierRetentionNumerics
open BinaryCarrierS16RouteLocalCertificates
open BinaryCarrierS16TaggedPositiveRoutes
open BinaryDegreeEightPhysicalAnalyticClosure
open BinaryS16CanonicalCarrierProfile
open BinaryS16DirectCertifiedOrbitProfile
open FusionOrbitQuotientAxisTransport

/-- The quotient-identity cell gives a certified zero-support slot on every
normal axis of a critical original action. -/
def criticalCertifiedSlot
    (i : CriticalActionKind)
    (N : Subgroup (criticalActionSubgroup i)) (hN : N.Normal) :
    CertifiedSlot N (cellHalfDegree (.inl i)) 0 := by
  letI : N.Normal := hN
  let A : AxisSlot (criticalActionSubgroup i) N :=
    { slot := @quotientIdentitySlot (.inl i) N hN
      sourceEquiv := MulEquiv.refl (criticalActionSubgroup i)
      kernel := by
        have hid : N.map (MulEquiv.refl
            (criticalActionSubgroup i)).toMonoidHom = N := by
          ext x
          constructor
          · rintro ⟨y,hy,rfl⟩
            exact hy
          · intro hx
            exact ⟨x,hx,rfl⟩
        exact hid.trans
          (@quotientIdentitySlot_alpha_ker (.inl i) N hN).symm }
  exact CertifiedSlot.ofCertificate A
    (@criticalIdentity_certificate i N hN)
    (Nat.le_refl 0) (Nat.le_refl 0)

/-- Equality of joint local models induces the corresponding equivalence of
their selected action groups, with the point-type transport kept internal. -/
def localModelActionEquivOfEq
    {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))}
    {o : OrbitProfileFromOrbits.Orbit H}
    {L M : BinaryS16JointOrbitData.LocalModel H o} (h : L = M) :
    L.action ≃* M.action := by
  subst M
  exact MulEquiv.refl _

section CriticalRoute

variable {n : ℕ}
variable (H : Subgroup (Equiv.Perm (Fin n)))
variable (hH : ResidualSector H)

/-- The critical C2 certificate routes to the quotient-identity slot on the
same canonical occurrence axis. -/
def criticalRouteC2
    (o : OrbitProfileFromOrbits.Orbit H)
    (j : Fin ((BinaryS16JointOrbitData.data H hH).multiplicity o))
    (e : criticalActionPoints .c2 ≃ o.orbit)
    (he : relabelSubgroup e (criticalActionSubgroup .c2) =
      OrbitProfileFromOrbits.orbitImage H o)
    (hp : profile H hH o = .c2 e he) :
    CertifiedSlot
      (CanonicalOrbitWord.axis
        (BinaryS16JointOrbitData.Points H hH)
        (BinaryS16JointOrbitData.action H hH) H
        (BinaryS16JointOrbitData.data H hH) ⟨o,j⟩)
      (BinaryS16JointOrbitData.parameter H hH o)
      (BinaryS16JointOrbitData.oldSupportAt H hH o) := by
  let N := CanonicalOrbitWord.axis
    (BinaryS16JointOrbitData.Points H hH)
    (BinaryS16JointOrbitData.action H hH) H
    (BinaryS16JointOrbitData.data H hH) ⟨o,j⟩
  have hN : N.Normal := CanonicalOrbitWord.axis_normal
    (BinaryS16JointOrbitData.Points H hH)
    (BinaryS16JointOrbitData.action H hH) H
    (BinaryS16JointOrbitData.data H hH) ⟨o,j⟩
  have hmodel : BinaryS16JointOrbitData.localModel H hH o =
      BinaryS16JointOrbitData.certificateLocalModel H (.c2 e he) := by
    unfold BinaryS16JointOrbitData.localModel
    exact congrArg
      (fun C => BinaryS16JointOrbitData.certificateLocalModel H C) hp
  let E := localModelActionEquivOfEq hmodel
  let M := N.map E.toMonoidHom
  have hM : M.Normal := Subgroup.Normal.map hN E.toMonoidHom E.surjective
  let S : CertifiedSlot N 1 0 :=
    (criticalCertifiedSlot .c2 M hM).pullback E
  exact S.reindex
    (by simp [BinaryS16JointOrbitData.parameter,hp,
      BinaryS16JointOrbitData.certificateParameter])
    (by simp [BinaryS16JointOrbitData.oldSupportAt,hp,
      BinaryS16JointOrbitData.certificateOldSupport])


/-- The critical V4 certificate routes to the quotient-identity slot on the
same canonical occurrence axis. -/
def criticalRouteV4
    (o : OrbitProfileFromOrbits.Orbit H)
    (j : Fin ((BinaryS16JointOrbitData.data H hH).multiplicity o))
    (e : criticalActionPoints .v4 ≃ o.orbit)
    (he : relabelSubgroup e (criticalActionSubgroup .v4) =
      OrbitProfileFromOrbits.orbitImage H o)
    (hp : profile H hH o = .v4 e he) :
    CertifiedSlot
      (CanonicalOrbitWord.axis
        (BinaryS16JointOrbitData.Points H hH)
        (BinaryS16JointOrbitData.action H hH) H
        (BinaryS16JointOrbitData.data H hH) ⟨o,j⟩)
      (BinaryS16JointOrbitData.parameter H hH o)
      (BinaryS16JointOrbitData.oldSupportAt H hH o) := by
  let N := CanonicalOrbitWord.axis
    (BinaryS16JointOrbitData.Points H hH)
    (BinaryS16JointOrbitData.action H hH) H
    (BinaryS16JointOrbitData.data H hH) ⟨o,j⟩
  have hN : N.Normal := CanonicalOrbitWord.axis_normal
    (BinaryS16JointOrbitData.Points H hH)
    (BinaryS16JointOrbitData.action H hH) H
    (BinaryS16JointOrbitData.data H hH) ⟨o,j⟩
  have hmodel : BinaryS16JointOrbitData.localModel H hH o =
      BinaryS16JointOrbitData.certificateLocalModel H (.v4 e he) := by
    unfold BinaryS16JointOrbitData.localModel
    exact congrArg
      (fun C => BinaryS16JointOrbitData.certificateLocalModel H C) hp
  let E := localModelActionEquivOfEq hmodel
  let M := N.map E.toMonoidHom
  have hM : M.Normal := Subgroup.Normal.map hN E.toMonoidHom E.surjective
  let S : CertifiedSlot N 2 0 :=
    (criticalCertifiedSlot .v4 M hM).pullback E
  exact S.reindex
    (by simp [BinaryS16JointOrbitData.parameter,hp,
      BinaryS16JointOrbitData.certificateParameter])
    (by simp [BinaryS16JointOrbitData.oldSupportAt,hp,
      BinaryS16JointOrbitData.certificateOldSupport])


/-- The critical D8 certificate routes to the quotient-identity slot on the
same canonical occurrence axis. -/
def criticalRouteD8
    (o : OrbitProfileFromOrbits.Orbit H)
    (j : Fin ((BinaryS16JointOrbitData.data H hH).multiplicity o))
    (e : criticalActionPoints .d8 ≃ o.orbit)
    (he : relabelSubgroup e (criticalActionSubgroup .d8) =
      OrbitProfileFromOrbits.orbitImage H o)
    (hp : profile H hH o = .d8 e he) :
    CertifiedSlot
      (CanonicalOrbitWord.axis
        (BinaryS16JointOrbitData.Points H hH)
        (BinaryS16JointOrbitData.action H hH) H
        (BinaryS16JointOrbitData.data H hH) ⟨o,j⟩)
      (BinaryS16JointOrbitData.parameter H hH o)
      (BinaryS16JointOrbitData.oldSupportAt H hH o) := by
  let N := CanonicalOrbitWord.axis
    (BinaryS16JointOrbitData.Points H hH)
    (BinaryS16JointOrbitData.action H hH) H
    (BinaryS16JointOrbitData.data H hH) ⟨o,j⟩
  have hN : N.Normal := CanonicalOrbitWord.axis_normal
    (BinaryS16JointOrbitData.Points H hH)
    (BinaryS16JointOrbitData.action H hH) H
    (BinaryS16JointOrbitData.data H hH) ⟨o,j⟩
  have hmodel : BinaryS16JointOrbitData.localModel H hH o =
      BinaryS16JointOrbitData.certificateLocalModel H (.d8 e he) := by
    unfold BinaryS16JointOrbitData.localModel
    exact congrArg
      (fun C => BinaryS16JointOrbitData.certificateLocalModel H C) hp
  let E := localModelActionEquivOfEq hmodel
  let M := N.map E.toMonoidHom
  have hM : M.Normal := Subgroup.Normal.map hN E.toMonoidHom E.surjective
  let S : CertifiedSlot N 2 0 :=
    (criticalCertifiedSlot .d8 M hM).pullback E
  exact S.reindex
    (by simp [BinaryS16JointOrbitData.parameter,hp,
      BinaryS16JointOrbitData.certificateParameter])
    (by simp [BinaryS16JointOrbitData.oldSupportAt,hp,
      BinaryS16JointOrbitData.certificateOldSupport])


/-- The critical E8 certificate routes to the quotient-identity slot on the
same canonical occurrence axis. -/
def criticalRouteE8
    (o : OrbitProfileFromOrbits.Orbit H)
    (j : Fin ((BinaryS16JointOrbitData.data H hH).multiplicity o))
    (e : criticalActionPoints .e8 ≃ o.orbit)
    (he : relabelSubgroup e (criticalActionSubgroup .e8) =
      OrbitProfileFromOrbits.orbitImage H o)
    (hp : profile H hH o = .e8 e he) :
    CertifiedSlot
      (CanonicalOrbitWord.axis
        (BinaryS16JointOrbitData.Points H hH)
        (BinaryS16JointOrbitData.action H hH) H
        (BinaryS16JointOrbitData.data H hH) ⟨o,j⟩)
      (BinaryS16JointOrbitData.parameter H hH o)
      (BinaryS16JointOrbitData.oldSupportAt H hH o) := by
  let N := CanonicalOrbitWord.axis
    (BinaryS16JointOrbitData.Points H hH)
    (BinaryS16JointOrbitData.action H hH) H
    (BinaryS16JointOrbitData.data H hH) ⟨o,j⟩
  have hN : N.Normal := CanonicalOrbitWord.axis_normal
    (BinaryS16JointOrbitData.Points H hH)
    (BinaryS16JointOrbitData.action H hH) H
    (BinaryS16JointOrbitData.data H hH) ⟨o,j⟩
  have hmodel : BinaryS16JointOrbitData.localModel H hH o =
      BinaryS16JointOrbitData.certificateLocalModel H (.e8 e he) := by
    unfold BinaryS16JointOrbitData.localModel
    exact congrArg
      (fun C => BinaryS16JointOrbitData.certificateLocalModel H C) hp
  let E := localModelActionEquivOfEq hmodel
  let M := N.map E.toMonoidHom
  have hM : M.Normal := Subgroup.Normal.map hN E.toMonoidHom E.surjective
  let S : CertifiedSlot N 4 0 :=
    (criticalCertifiedSlot .e8 M hM).pullback E
  exact S.reindex
    (by simp [BinaryS16JointOrbitData.parameter,hp,
      BinaryS16JointOrbitData.certificateParameter])
    (by simp [BinaryS16JointOrbitData.oldSupportAt,hp,
      BinaryS16JointOrbitData.certificateOldSupport])

end CriticalRoute

section PositiveRoute

variable {n : ℕ}
variable (H : Subgroup (Equiv.Perm (Fin n)))
variable (hH : ResidualSector H)

/-- The unique occurrence in a literal-orbit label fibre is that orbit with
the reflexive label equality. -/
theorem occurrence_eq_self
    (q : Σ o, Fin ((BinaryS16JointOrbitData.data H hH).multiplicity o)) :
    (BinaryS16JointOrbitData.data H hH).occurrence q.1 q.2 =
      ⟨q.1,rfl⟩ := by
  apply Subtype.ext
  simpa [BinaryS16JointOrbitData.data] using
    ((BinaryS16JointOrbitData.data H hH).occurrence q.1 q.2).property

@[simp] theorem exactOrbitChart_transport_point_coe
    {q o : OrbitProfileFromOrbits.Orbit H}
    {P : Type} {U : Subgroup (Equiv.Perm P)}
    (ho : q = o) (C : BinaryS16JointOrbitData.ExactOrbitChart H q P U)
    (x : P) :
    (((BinaryS16JointOrbitData.ExactOrbitChart.transport H ho C).pointEquiv x :
        o.orbit) : Fin n) = ((C.pointEquiv x : q.orbit) : Fin n) := by
  subst o
  rfl

/-- On underlying original points, a fibre chart for the identity orbit label
is the chart stored at that literal orbit. -/
theorem fiberChart_point_coe
    (o : OrbitProfileFromOrbits.Orbit H)
    (r : (BinaryS16JointOrbitData.data H hH).Fiber o)
    (x : BinaryS16JointOrbitData.Points H hH o) :
    ((((BinaryS16JointOrbitData.data H hH).fiberChart o r) x :
        r.1.orbit) : Fin n) =
      (((BinaryS16JointOrbitData.localModel H hH o).chart.pointEquiv x :
        o.orbit) : Fin n) := by
  rcases r with ⟨r,hr⟩
  subst o
  rfl

/-- The local chart selected by the singleton occurrence is the chart stored
in its joint local model, transported along the canonical orbit-index
equality. -/
theorem localChart_eq_transportedModelChart
    (q : Σ o, Fin ((BinaryS16JointOrbitData.data H hH).multiplicity o)) :
    (BinaryS16JointOrbitData.data H hH).localChart q.1 q.2 =
      (BinaryS16JointOrbitData.ExactOrbitChart.transport H
        (BinaryS16JointOrbitData.orbitIndex_eq_fst H hH q).symm
        (BinaryS16JointOrbitData.localModel H hH q.1).chart).pointEquiv := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  rw [exactOrbitChart_transport_point_coe]
  exact fiberChart_point_coe H hH q.1
    ((BinaryS16JointOrbitData.data H hH).occurrence q.1 q.2) x

/-- Simultaneously transporting the point type, action, and exact orbit chart
of an equal local model transports its selected deleted axis by the induced
action equivalence. -/
theorem localModelDeletedAxis_map_eq
    {o o' : OrbitProfileFromOrbits.Orbit H}
    {L M : BinaryS16JointOrbitData.LocalModel H o}
    (hLM : L = M) (ho : o = o')
    {Z : Type} [Fintype Z]
    (eC : Z ≃ ↥((FusionOrbitProfileChart.orbitSubaction H o')ᶜ)) :
    ((fusionDeletedModel L.action
        (relabelSubgroup
          (FusionOrbitProfileChart.chart H o'
            (BinaryS16JointOrbitData.ExactOrbitChart.transport H ho
              L.chart).pointEquiv eC).symm H)).goursatFst).map
          (localModelActionEquivOfEq hLM).toMonoidHom =
      (fusionDeletedModel M.action
        (relabelSubgroup
          (FusionOrbitProfileChart.chart H o'
            (BinaryS16JointOrbitData.ExactOrbitChart.transport H ho
              M.chart).pointEquiv eC).symm H)).goursatFst := by
  subst M
  let K := (fusionDeletedModel L.action
    (relabelSubgroup
      (FusionOrbitProfileChart.chart H o'
        (BinaryS16JointOrbitData.ExactOrbitChart.transport H ho
          L.chart).pointEquiv eC).symm H)).goursatFst
  have hid : K.map (MulEquiv.refl L.action).toMonoidHom = K := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      exact ⟨x,hx,rfl⟩
  simpa [K,localModelActionEquivOfEq] using hid

/-- The positive width-four certificate transports its stored physical slot
to the canonical occurrence axis. -/
private def positiveRouteC4Core
    (o : OrbitProfileFromOrbits.Orbit H)
    (j : Fin ((BinaryS16JointOrbitData.data H hH).multiplicity o))
    (W : SmallOrbitWitness 4 H)
    (hpoint : Quotient.mk'' W.point = o)
    (R : DegreeFourRoute W)
    (hp : profile H hH o = .cyclicFour W hpoint R) :
    CertifiedSlot
      (CanonicalOrbitWord.axis
        (BinaryS16JointOrbitData.Points H hH)
        (BinaryS16JointOrbitData.action H hH) H
        (BinaryS16JointOrbitData.data H hH) ⟨o,j⟩)
      2 2 := by
  let q := (⟨o,j⟩ :
    Σ o, Fin ((BinaryS16JointOrbitData.data H hH).multiplicity o))
  let L := BinaryS16JointOrbitData.localModel H hH o
  let M := BinaryS16JointOrbitData.certificateLocalModel H
    (.cyclicFour W hpoint R)
  have hmodel : BinaryS16JointOrbitData.localModel H hH o =
      BinaryS16JointOrbitData.certificateLocalModel H
        (.cyclicFour W hpoint R) := by
    unfold BinaryS16JointOrbitData.localModel
    exact congrArg
      (fun C => BinaryS16JointOrbitData.certificateLocalModel H C) hp
  let E := localModelActionEquivOfEq hmodel
  let ho : o = (BinaryS16JointOrbitData.data H hH).orbitIndex q :=
    (BinaryS16JointOrbitData.orbitIndex_eq_fst H hH q).symm
  have hselected :
      (Quotient.mk'' W.point : OrbitProfileFromOrbits.Orbit H) =
        (BinaryS16JointOrbitData.data H hH).orbitIndex q :=
    hpoint.trans ho
  let D := BinaryS16JointOrbitData.ExactOrbitChart.transport H ho M.chart
  let T := transportData H W.point W.orbit_card hselected
    D.pointEquiv W.action D.image_eq
  let F := E.trans T.E
  apply certifiedSlotOfCanonicalFusionAxis
    (BinaryS16JointOrbitData.Points H hH)
    (BinaryS16JointOrbitData.action H hH) H
    (BinaryS16JointOrbitData.data H hH) q T.eC F W.axis
  · have hchart :
        BinaryCarrierCanonicalOrbitAxisBridge.selectedChart
            (BinaryS16JointOrbitData.Points H hH)
            (BinaryS16JointOrbitData.action H hH) H
            (BinaryS16JointOrbitData.data H hH) q T.eC =
          FusionOrbitProfileChart.chart H
            ((BinaryS16JointOrbitData.data H hH).orbitIndex q)
            (BinaryS16JointOrbitData.ExactOrbitChart.transport H ho
              L.chart).pointEquiv T.eC := by
      unfold BinaryCarrierCanonicalOrbitAxisBridge.selectedChart
      rw [localChart_eq_transportedModelChart H hH q]
    rw [hchart]
    change ((fusionDeletedModel L.action
      (relabelSubgroup
        (FusionOrbitProfileChart.chart H
          ((BinaryS16JointOrbitData.data H hH).orbitIndex q)
          (BinaryS16JointOrbitData.ExactOrbitChart.transport H ho
            L.chart).pointEquiv T.eC).symm H)).goursatFst).map
        F.toMonoidHom = W.axis
    dsimp [F]
    rw [← Subgroup.map_map]
    calc
      (((fusionDeletedModel L.action
              (relabelSubgroup
                (FusionOrbitProfileChart.chart H
                  ((BinaryS16JointOrbitData.data H hH).orbitIndex q)
                  (BinaryS16JointOrbitData.ExactOrbitChart.transport H ho
                    L.chart).pointEquiv T.eC).symm H)).goursatFst).map
              E.toMonoidHom).map T.E.toMonoidHom =
          ((fusionDeletedModel M.action
              (relabelSubgroup
                (FusionOrbitProfileChart.chart H
                  ((BinaryS16JointOrbitData.data H hH).orbitIndex q)
                  D.pointEquiv T.eC).symm H)).goursatFst).map
              T.E.toMonoidHom := by
            rw [localModelDeletedAxis_map_eq H hmodel ho T.eC]
      _ = W.axis := by simpa [M] using T.axis_eq
  · exact R.certified.toCertifiedSlot

/-- The width-four core, reindexed by the two certificate-dependent numerical
functions without changing its physical slot. -/
def positiveRouteC4
    (o : OrbitProfileFromOrbits.Orbit H)
    (j : Fin ((BinaryS16JointOrbitData.data H hH).multiplicity o))
    (W : SmallOrbitWitness 4 H)
    (hpoint : Quotient.mk'' W.point = o)
    (R : DegreeFourRoute W)
    (hp : profile H hH o = .cyclicFour W hpoint R) :
    CertifiedSlot
      (CanonicalOrbitWord.axis
        (BinaryS16JointOrbitData.Points H hH)
        (BinaryS16JointOrbitData.action H hH) H
        (BinaryS16JointOrbitData.data H hH) ⟨o,j⟩)
      (BinaryS16JointOrbitData.parameter H hH o)
      (BinaryS16JointOrbitData.oldSupportAt H hH o) :=
  (positiveRouteC4Core H hH o j W hpoint R hp).reindex
    (by simp [BinaryS16JointOrbitData.parameter,hp,
      BinaryS16JointOrbitData.certificateParameter])
    (by simp [BinaryS16JointOrbitData.oldSupportAt,hp,
      BinaryS16JointOrbitData.certificateOldSupport])

/-- Canonical-axis transport and numerical reindexing leave the literal
physical slot of a width-four route unchanged. -/
@[simp] theorem positiveRouteC4_axisSlot_slot
    (o : OrbitProfileFromOrbits.Orbit H)
    (j : Fin ((BinaryS16JointOrbitData.data H hH).multiplicity o))
    (W : SmallOrbitWitness 4 H)
    (hpoint : Quotient.mk'' W.point = o)
    (R : DegreeFourRoute W)
    (hp : profile H hH o = .cyclicFour W hpoint R) :
    (positiveRouteC4 H hH o j W hpoint R hp).axisSlot.slot =
      R.certified.axisSlot.slot := by
  unfold positiveRouteC4
  simp only [CertifiedSlot.reindex_axisSlot_slot]
  unfold positiveRouteC4Core
  simp


/-- The positive degree-eight certificate transports its stored physical slot
to the canonical occurrence axis. -/
private def positiveRouteC8Core
    (o : OrbitProfileFromOrbits.Orbit H)
    (j : Fin ((BinaryS16JointOrbitData.data H hH).multiplicity o))
    (W : BinaryDegreeEightNormalizerSaturatedDirect.OrbitWitness H)
    (hpoint : Quotient.mk'' W.point = o)
    (R : DegreeEightRoute W.action W.axis)
    (hp : profile H hH o = .carrier8 W hpoint R) :
    CertifiedSlot
      (CanonicalOrbitWord.axis
        (BinaryS16JointOrbitData.Points H hH)
        (BinaryS16JointOrbitData.action H hH) H
        (BinaryS16JointOrbitData.data H hH) ⟨o,j⟩)
      4 4 := by
  let q := (⟨o,j⟩ :
    Σ o, Fin ((BinaryS16JointOrbitData.data H hH).multiplicity o))
  let L := BinaryS16JointOrbitData.localModel H hH o
  let M := BinaryS16JointOrbitData.certificateLocalModel H
    (.carrier8 W hpoint R)
  have hmodel : BinaryS16JointOrbitData.localModel H hH o =
      BinaryS16JointOrbitData.certificateLocalModel H
        (.carrier8 W hpoint R) := by
    unfold BinaryS16JointOrbitData.localModel
    exact congrArg
      (fun C => BinaryS16JointOrbitData.certificateLocalModel H C) hp
  let E := localModelActionEquivOfEq hmodel
  let ho : o = (BinaryS16JointOrbitData.data H hH).orbitIndex q :=
    (BinaryS16JointOrbitData.orbitIndex_eq_fst H hH q).symm
  have hselected :
      (Quotient.mk'' W.point : OrbitProfileFromOrbits.Orbit H) =
        (BinaryS16JointOrbitData.data H hH).orbitIndex q :=
    hpoint.trans ho
  let D := BinaryS16JointOrbitData.ExactOrbitChart.transport H ho M.chart
  let T := transportData H W.point W.orbit_card hselected
    D.pointEquiv W.action D.image_eq
  let F := E.trans T.E
  apply certifiedSlotOfCanonicalFusionAxis
    (BinaryS16JointOrbitData.Points H hH)
    (BinaryS16JointOrbitData.action H hH) H
    (BinaryS16JointOrbitData.data H hH) q T.eC F W.axis
  · have hchart :
        BinaryCarrierCanonicalOrbitAxisBridge.selectedChart
            (BinaryS16JointOrbitData.Points H hH)
            (BinaryS16JointOrbitData.action H hH) H
            (BinaryS16JointOrbitData.data H hH) q T.eC =
          FusionOrbitProfileChart.chart H
            ((BinaryS16JointOrbitData.data H hH).orbitIndex q)
            (BinaryS16JointOrbitData.ExactOrbitChart.transport H ho
              L.chart).pointEquiv T.eC := by
      unfold BinaryCarrierCanonicalOrbitAxisBridge.selectedChart
      rw [localChart_eq_transportedModelChart H hH q]
    rw [hchart]
    change ((fusionDeletedModel L.action
      (relabelSubgroup
        (FusionOrbitProfileChart.chart H
          ((BinaryS16JointOrbitData.data H hH).orbitIndex q)
          (BinaryS16JointOrbitData.ExactOrbitChart.transport H ho
            L.chart).pointEquiv T.eC).symm H)).goursatFst).map
        F.toMonoidHom = W.axis
    dsimp [F]
    rw [← Subgroup.map_map]
    calc
      (((fusionDeletedModel L.action
              (relabelSubgroup
                (FusionOrbitProfileChart.chart H
                  ((BinaryS16JointOrbitData.data H hH).orbitIndex q)
                  (BinaryS16JointOrbitData.ExactOrbitChart.transport H ho
                    L.chart).pointEquiv T.eC).symm H)).goursatFst).map
              E.toMonoidHom).map T.E.toMonoidHom =
          ((fusionDeletedModel M.action
              (relabelSubgroup
                (FusionOrbitProfileChart.chart H
                  ((BinaryS16JointOrbitData.data H hH).orbitIndex q)
                  D.pointEquiv T.eC).symm H)).goursatFst).map
              T.E.toMonoidHom := by
            rw [localModelDeletedAxis_map_eq H hmodel ho T.eC]
      _ = W.axis := by simpa [M] using T.axis_eq
  · exact R.certified.toCertifiedSlot


/-- The degree-eight core, reindexed without changing its physical slot. -/
def positiveRouteC8
    (o : OrbitProfileFromOrbits.Orbit H)
    (j : Fin ((BinaryS16JointOrbitData.data H hH).multiplicity o))
    (W : BinaryDegreeEightNormalizerSaturatedDirect.OrbitWitness H)
    (hpoint : Quotient.mk'' W.point = o)
    (R : DegreeEightRoute W.action W.axis)
    (hp : profile H hH o = .carrier8 W hpoint R) :
    CertifiedSlot
      (CanonicalOrbitWord.axis
        (BinaryS16JointOrbitData.Points H hH)
        (BinaryS16JointOrbitData.action H hH) H
        (BinaryS16JointOrbitData.data H hH) ⟨o,j⟩)
      (BinaryS16JointOrbitData.parameter H hH o)
      (BinaryS16JointOrbitData.oldSupportAt H hH o) :=
  (positiveRouteC8Core H hH o j W hpoint R hp).reindex
    (by simp [BinaryS16JointOrbitData.parameter,hp,
      BinaryS16JointOrbitData.certificateParameter])
    (by simp [BinaryS16JointOrbitData.oldSupportAt,hp,
      BinaryS16JointOrbitData.certificateOldSupport])

/-- Canonical-axis transport and numerical reindexing leave the literal
physical slot of a degree-eight route unchanged. -/
@[simp] theorem positiveRouteC8_axisSlot_slot
    (o : OrbitProfileFromOrbits.Orbit H)
    (j : Fin ((BinaryS16JointOrbitData.data H hH).multiplicity o))
    (W : BinaryDegreeEightNormalizerSaturatedDirect.OrbitWitness H)
    (hpoint : Quotient.mk'' W.point = o)
    (R : DegreeEightRoute W.action W.axis)
    (hp : profile H hH o = .carrier8 W hpoint R) :
    (positiveRouteC8 H hH o j W hpoint R hp).axisSlot.slot =
      R.certified.axisSlot.slot := by
  unfold positiveRouteC8
  simp only [CertifiedSlot.reindex_axisSlot_slot]
  unfold positiveRouteC8Core
  simp

private def positiveRouteC16Core
    (o : OrbitProfileFromOrbits.Orbit H)
    (j : Fin ((BinaryS16JointOrbitData.data H hH).multiplicity o))
    (W : BinaryDegree16PhysicalAnalyticClosure.OrbitWitness H)
    (hpoint : Quotient.mk'' W.point = o)
    (R : DegreeSixteenRoute W.action W.axis)
    (hp : profile H hH o = .carrier16 W hpoint R) :
    CertifiedSlot
      (CanonicalOrbitWord.axis
        (BinaryS16JointOrbitData.Points H hH)
        (BinaryS16JointOrbitData.action H hH) H
        (BinaryS16JointOrbitData.data H hH) ⟨o,j⟩)
      8 8 := by
  let q := (⟨o,j⟩ :
    Σ o, Fin ((BinaryS16JointOrbitData.data H hH).multiplicity o))
  let L := BinaryS16JointOrbitData.localModel H hH o
  let M := BinaryS16JointOrbitData.certificateLocalModel H
    (.carrier16 W hpoint R)
  have hmodel : BinaryS16JointOrbitData.localModel H hH o =
      BinaryS16JointOrbitData.certificateLocalModel H
        (.carrier16 W hpoint R) := by
    unfold BinaryS16JointOrbitData.localModel
    exact congrArg
      (fun C => BinaryS16JointOrbitData.certificateLocalModel H C) hp
  let E := localModelActionEquivOfEq hmodel
  let ho : o = (BinaryS16JointOrbitData.data H hH).orbitIndex q :=
    (BinaryS16JointOrbitData.orbitIndex_eq_fst H hH q).symm
  have hselected :
      (Quotient.mk'' W.point : OrbitProfileFromOrbits.Orbit H) =
        (BinaryS16JointOrbitData.data H hH).orbitIndex q :=
    hpoint.trans ho
  let D := BinaryS16JointOrbitData.ExactOrbitChart.transport H ho M.chart
  let T := transportData H W.point W.orbit_card hselected
    D.pointEquiv W.action D.image_eq
  let F := E.trans T.E
  apply certifiedSlotOfCanonicalFusionAxis
    (BinaryS16JointOrbitData.Points H hH)
    (BinaryS16JointOrbitData.action H hH) H
    (BinaryS16JointOrbitData.data H hH) q T.eC F W.axis
  · have hchart :
        BinaryCarrierCanonicalOrbitAxisBridge.selectedChart
            (BinaryS16JointOrbitData.Points H hH)
            (BinaryS16JointOrbitData.action H hH) H
            (BinaryS16JointOrbitData.data H hH) q T.eC =
          FusionOrbitProfileChart.chart H
            ((BinaryS16JointOrbitData.data H hH).orbitIndex q)
            (BinaryS16JointOrbitData.ExactOrbitChart.transport H ho
              L.chart).pointEquiv T.eC := by
      unfold BinaryCarrierCanonicalOrbitAxisBridge.selectedChart
      rw [localChart_eq_transportedModelChart H hH q]
    rw [hchart]
    change ((fusionDeletedModel L.action
      (relabelSubgroup
        (FusionOrbitProfileChart.chart H
          ((BinaryS16JointOrbitData.data H hH).orbitIndex q)
          (BinaryS16JointOrbitData.ExactOrbitChart.transport H ho
            L.chart).pointEquiv T.eC).symm H)).goursatFst).map
        F.toMonoidHom = W.axis
    dsimp [F]
    rw [← Subgroup.map_map]
    calc
      (((fusionDeletedModel L.action
              (relabelSubgroup
                (FusionOrbitProfileChart.chart H
                  ((BinaryS16JointOrbitData.data H hH).orbitIndex q)
                  (BinaryS16JointOrbitData.ExactOrbitChart.transport H ho
                    L.chart).pointEquiv T.eC).symm H)).goursatFst).map
              E.toMonoidHom).map T.E.toMonoidHom =
          ((fusionDeletedModel M.action
              (relabelSubgroup
                (FusionOrbitProfileChart.chart H
                  ((BinaryS16JointOrbitData.data H hH).orbitIndex q)
                  D.pointEquiv T.eC).symm H)).goursatFst).map
              T.E.toMonoidHom := by
            rw [localModelDeletedAxis_map_eq H hmodel ho T.eC]
      _ = W.axis := by simpa [M] using T.axis_eq
  · exact R.certified.toCertifiedSlot

/-- The degree-sixteen core, reindexed without changing its physical slot. -/
def positiveRouteC16
    (o : OrbitProfileFromOrbits.Orbit H)
    (j : Fin ((BinaryS16JointOrbitData.data H hH).multiplicity o))
    (W : BinaryDegree16PhysicalAnalyticClosure.OrbitWitness H)
    (hpoint : Quotient.mk'' W.point = o)
    (R : DegreeSixteenRoute W.action W.axis)
    (hp : profile H hH o = .carrier16 W hpoint R) :
    CertifiedSlot
      (CanonicalOrbitWord.axis
        (BinaryS16JointOrbitData.Points H hH)
        (BinaryS16JointOrbitData.action H hH) H
        (BinaryS16JointOrbitData.data H hH) ⟨o,j⟩)
      (BinaryS16JointOrbitData.parameter H hH o)
      (BinaryS16JointOrbitData.oldSupportAt H hH o) :=
  (positiveRouteC16Core H hH o j W hpoint R hp).reindex
    (by simp [BinaryS16JointOrbitData.parameter,hp,
      BinaryS16JointOrbitData.certificateParameter])
    (by simp [BinaryS16JointOrbitData.oldSupportAt,hp,
      BinaryS16JointOrbitData.certificateOldSupport])

/-- Canonical-axis transport and numerical reindexing leave the literal
physical slot of a degree-sixteen route unchanged. -/
@[simp] theorem positiveRouteC16_axisSlot_slot
    (o : OrbitProfileFromOrbits.Orbit H)
    (j : Fin ((BinaryS16JointOrbitData.data H hH).multiplicity o))
    (W : BinaryDegree16PhysicalAnalyticClosure.OrbitWitness H)
    (hpoint : Quotient.mk'' W.point = o)
    (R : DegreeSixteenRoute W.action W.axis)
    (hp : profile H hH o = .carrier16 W hpoint R) :
    (positiveRouteC16 H hH o j W hpoint R hp).axisSlot.slot =
      R.certified.axisSlot.slot := by
  unfold positiveRouteC16
  simp only [CertifiedSlot.reindex_axisSlot_slot]
  unfold positiveRouteC16Core
  simp

end PositiveRoute

section CompleteRouting

variable {n : ℕ}
variable (H : Subgroup (Equiv.Perm (Fin n)))
variable (hH : ResidualSector H)

/-- Route one explicitly supplied occurrence certificate.  Keeping the
certificate as an argument gives downstream point-chart constructions a
computational interface: the routed slot and its source point type reduce by
the same case split. -/
def routeCertificate
    (q : Σ o, Fin ((BinaryS16JointOrbitData.data H hH).multiplicity o))
    (C : OrbitCertificate H q.1) (hp : profile H hH q.1 = C) :
    CertifiedSlot
      (CanonicalOrbitWord.axis
        (BinaryS16JointOrbitData.Points H hH)
        (BinaryS16JointOrbitData.action H hH) H
        (BinaryS16JointOrbitData.data H hH) q)
      (BinaryS16JointOrbitData.parameter H hH q.1)
      (BinaryS16JointOrbitData.oldSupportAt H hH q.1) :=
  match C with
    | .c2 e he => criticalRouteC2 H hH q.1 q.2 e he hp
    | .v4 e he => criticalRouteV4 H hH q.1 q.2 e he hp
    | .d8 e he => criticalRouteD8 H hH q.1 q.2 e he hp
    | .e8 e he => criticalRouteE8 H hH q.1 q.2 e he hp
    | .cyclicFour W hpoint S =>
        positiveRouteC4 H hH q.1 q.2 W hpoint S hp
    | .carrier8 W hpoint S =>
        positiveRouteC8 H hH q.1 q.2 W hpoint S hp
    | .carrier16 W hpoint S =>
        positiveRouteC16 H hH q.1 q.2 W hpoint S hp

/-- The complete deterministic routing of every literal quotient-orbit
occurrence.  Every branch is read from the same certificate that supplied its
point action, exact chart, parameter, and old support. -/
def axisRouting : BinaryS16JointOrbitData.AxisRouting H hH := fun q =>
  routeCertificate H hH q (profile H hH q.1) rfl

end CompleteRouting

end SymmetricSubgroupAsymptotics.BinaryS16JointAxisRouting

end
