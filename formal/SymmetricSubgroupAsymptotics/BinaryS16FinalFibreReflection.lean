import SymmetricSubgroupAsymptotics.BinaryCarrierFusionEmbeddingFormula
import SymmetricSubgroupAsymptotics.BinaryCarrierIdentityPresentationNaturality
import SymmetricSubgroupAsymptotics.BinaryCarrierIndexedAlignedWordReflection
import SymmetricSubgroupAsymptotics.BinaryCarrierSlotCastNaturality
import SymmetricSubgroupAsymptotics.BinaryS16CommonSourceTransport
import SymmetricSubgroupAsymptotics.BinaryS16ExceptionalDisplayedAction
import SymmetricSubgroupAsymptotics.BinaryS16LocalActionAlignment
import SymmetricSubgroupAsymptotics.BinaryS16RouteActionNaturality
import SymmetricSubgroupAsymptotics.BinaryS16RouteMatching
import SymmetricSubgroupAsymptotics.BinaryS16TargetCastAccessor

/-!
# Final fibre reflection for the direct S16 carrier word

The source-orbit reindexing separates the last local comparison into two
literal branches.  A quotient-identity route uses the canonical conjugacy of
its local source actions and constructs its quotient square after the
replacement kernel is recovered.  A proper route is one of four fixed slots;
the retained mixed record identifies its source placement and displayed
point chart with literal transport of that fixed slot.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16FinalFibreReflection

open SymmetricSubgroupAsymptotics
open BinaryCarrierActualDecoratedProducer
open BinaryCarrierFusionEmbeddingFormula
open BinaryCarrierIdentityPresentationNaturality
open BinaryCarrierIndexedAlignedWordReflection
open BinaryCarrierIndexedKernelReflection
open BinaryCarrierKernelNaturalizedReflection
open BinaryCarrierMenuSlots
open BinaryCarrierOriginalLabelEmbedding
open BinaryCarrierSlotCastNaturality
open BinaryCarrierWordClosure
open BinaryCarrierCanonicalOrbitPhysicalEncoding
open BinaryS16CommonSourceTransport
open BinaryS16DirectPhysicalEncoding
open BinaryS16DirectPhysicalTarget
open BinaryS16ExceptionalDisplayedAction
open BinaryS16FusionNaturalPointChart
open BinaryS16JointOrbitData
open BinaryS16LocalActionAlignment
open BinaryS16RouteActionNaturality
open BinaryS16RouteMatching
open BinaryS16RouteSlotSkeleton
open BinaryS16SourceOrbitReindex

variable {N : ℕ} (C : BinaryS16DirectFixedSupportClosure.SupportIndex N)

abbrev Actual := BinaryS16DirectPhysicalTarget.Actual C

private theorem displayedPointEquivOfEq_comp
    {S T U : Slot} (h : S = T) (k : T = U)
    (z : Σ c : S.Cells,
      BinaryCarrierProfileTransport.mixturePoints (S.color c)) :
    displayedPointEquivOfEq k (displayedPointEquivOfEq h z) =
      displayedPointEquivOfEq (h.trans k) z := by
  subst T
  subst U
  rfl

/-- Literal slot transport commutes with the carrier action on its displayed
points. -/
private theorem displayedCarrierAction_cast {S T : Slot} (h : S = T)
    (p : S.carrier)
    (z : Σ c : S.Cells,
      BinaryCarrierProfileTransport.mixturePoints (S.color c)) :
    displayedPointEquivOfEq h (displayedCarrierAction S p z) =
      displayedCarrierAction T (carrierEquivOfEq h p)
        (displayedPointEquivOfEq h z) := by
  subst T
  rfl

/-- Eliminate orbit-label transport after any preceding point chart.  This
form is deliberately phrased at the composite boundary used by the retained
mixed record. -/
private theorem trans_exactOrbitChart_transport_point_coe
    {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}
    {q o : OrbitProfileFromOrbits.Orbit G}
    {A P : Type} {U : Subgroup (Equiv.Perm P)}
    (e : A ≃ P) (ho : q = o)
    (D : BinaryS16JointOrbitData.ExactOrbitChart G q P U) (x : A) :
    ((((e.trans
        (BinaryS16JointOrbitData.ExactOrbitChart.transport
          G ho D).pointEquiv) x : o.orbit) : Fin n)) =
      (((D.pointEquiv (e x) : q.orbit) : Fin n)) := by
  exact BinaryS16JointAxisRouting.exactOrbitChart_transport_point_coe
    G ho D (e x)

/-- Conjugating a permutation subgroup through two successive point charts
is the same group equivalence as conjugating through their composite. -/
private theorem relabelActionEquiv_trans
    {A B D : Type} (a : A ≃ B) (b : B ≃ D)
    (U : Subgroup (Equiv.Perm A))
    (V : Subgroup (Equiv.Perm B))
    (W : Subgroup (Equiv.Perm D))
    (hUV : relabelSubgroup a U = V)
    (hVW : relabelSubgroup b V = W) :
    (BinaryS16RouteActionNaturality.relabelActionEquiv a U V hUV).trans
        (BinaryS16RouteActionNaturality.relabelActionEquiv b V W hVW) =
      BinaryS16RouteActionNaturality.relabelActionEquiv (a.trans b) U W
        (by rw [← relabelSubgroup_trans, hUV, hVW]) := by
  apply MulEquiv.ext
  intro u
  apply Subtype.ext
  change b.permCongr (a.permCongr (u : Equiv.Perm A)) =
    (a.trans b).permCongr (u : Equiv.Perm A)
  apply Equiv.ext
  intro x
  simp [Equiv.permCongr_apply]

private theorem carrier8CertificateChart_coe
    {M : ℕ} {G : Subgroup (Equiv.Perm (Fin (2 * M)))}
    {o : OrbitProfileFromOrbits.Orbit G}
    (W : BinaryDegreeEightNormalizerSaturatedDirect.OrbitWitness G)
    (hpoint : Quotient.mk'' W.point = o)
    (R : BinaryCarrierS16TaggedPositiveRoutes.DegreeEightRoute
      W.action W.axis) (x : Fin 8) :
    ((((BinaryS16JointOrbitData.certificateLocalModel G
        (.carrier8 W hpoint R)).chart.pointEquiv x : o.orbit) : Fin (2 * M))) =
      (((FusionActualOrbitCharts.orbitEquiv
        G W.point W.orbit_card x : Fin (2 * M)))) := by
  exact BinaryS16JointAxisRouting.exactOrbitChart_transport_point_coe
    G hpoint
      ⟨FusionActualOrbitCharts.orbitEquiv G W.point W.orbit_card,
        BinaryS16JointOrbitData.witnessEight_image_eq G W⟩ x

private theorem carrier16CertificateChart_coe
    {M : ℕ} {G : Subgroup (Equiv.Perm (Fin (2 * M)))}
    {o : OrbitProfileFromOrbits.Orbit G}
    (W : BinaryDegree16PhysicalAnalyticClosure.OrbitWitness G)
    (hpoint : Quotient.mk'' W.point = o)
    (R : BinaryCarrierS16TaggedPositiveRoutes.DegreeSixteenRoute
      W.action W.axis) (x : Fin 16) :
    ((((BinaryS16JointOrbitData.certificateLocalModel G
        (.carrier16 W hpoint R)).chart.pointEquiv x : o.orbit) : Fin (2 * M))) =
      (((FusionActualOrbitCharts.orbitEquiv
        G W.point W.orbit_card x : Fin (2 * M)))) := by
  exact BinaryS16JointAxisRouting.exactOrbitChart_transport_point_coe
    G hpoint
      ⟨FusionActualOrbitCharts.orbitEquiv G W.point W.orbit_card,
        BinaryS16JointOrbitData.witnessSixteen_image_eq G W⟩ x

private theorem carrier8DisplayedCertificateChart_coe
    {M : ℕ} {G : Subgroup (Equiv.Perm (Fin (2 * M)))}
    {o : OrbitProfileFromOrbits.Orbit G}
    (W : BinaryDegreeEightNormalizerSaturatedDirect.OrbitWitness G)
    (hpoint : Quotient.mk'' W.point = o)
    (R : BinaryCarrierS16TaggedPositiveRoutes.DegreeEightRoute
      W.action W.axis)
    (z : Σ c : R.certified.axisSlot.slot.Cells,
      BinaryCarrierProfileTransport.mixturePoints
        (R.certified.axisSlot.slot.color c)) :
    ((((R.displayedPointEquiv.trans
        (BinaryS16JointOrbitData.certificateLocalModel G
          (.carrier8 W hpoint R)).chart.pointEquiv) z : o.orbit) :
      Fin (2 * M))) =
      (((FusionActualOrbitCharts.orbitEquiv
        G W.point W.orbit_card (R.displayedPointEquiv z) : Fin (2 * M)))) := by
  simpa only [Equiv.trans_apply] using
    carrier8CertificateChart_coe W hpoint R (R.displayedPointEquiv z)

private theorem carrier16DisplayedCertificateChart_coe
    {M : ℕ} {G : Subgroup (Equiv.Perm (Fin (2 * M)))}
    {o : OrbitProfileFromOrbits.Orbit G}
    (W : BinaryDegree16PhysicalAnalyticClosure.OrbitWitness G)
    (hpoint : Quotient.mk'' W.point = o)
    (R : BinaryCarrierS16TaggedPositiveRoutes.DegreeSixteenRoute
      W.action W.axis)
    (z : Σ c : R.certified.axisSlot.slot.Cells,
      BinaryCarrierProfileTransport.mixturePoints
        (R.certified.axisSlot.slot.color c)) :
    ((((R.displayedPointEquiv.trans
        (BinaryS16JointOrbitData.certificateLocalModel G
          (.carrier16 W hpoint R)).chart.pointEquiv) z : o.orbit) :
      Fin (2 * M))) =
      (((FusionActualOrbitCharts.orbitEquiv
        G W.point W.orbit_card (R.displayedPointEquiv z) : Fin (2 * M)))) := by
  simpa only [Equiv.trans_apply] using
    carrier16CertificateChart_coe W hpoint R (R.displayedPointEquiv z)

section Matched

variable {H K : Actual C}
variable (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
  BinaryS16DirectPhysicalEncoding.blocks C K)
variable (htarget : targetSubgroup C H = targetSubgroup C K)

abbrev eI : Occurrence C H ≃ Occurrence C K :=
  occurrenceEquiv C hblocks htarget

abbrev leftSlot (q : Occurrence C H) :=
  routeSlot (subgroup C H) (residualSector C H) q

abbrev rightSlot (q : Occurrence C H) :=
  routeSlot (subgroup C K) (residualSector C K) (eI C hblocks htarget q)

private def actionEquiv (q : Occurrence C H) :
    LocalAction C H q ≃* LocalAction C K (eI C hblocks htarget q) :=
  localActionEquiv C hblocks htarget
    (occurrenceLocalPointEquiv_action C hblocks htarget) q

/-- The literal equality of the two fixed proper slots. -/
private def properSlotEq (q : Occurrence C H) (e : Exceptional)
    (he : properKindAt (subgroup C H) (residualSector C H) q.1 = some e) :
    leftSlot C q = rightSlot C hblocks htarget q :=
  (matched_proper_slots C hblocks htarget q e he).1.trans
    (matched_proper_slots C hblocks htarget q e he).2.symm

/-- The displayed-point transport forced by the literal matched source orbit.
This is the point equivalence which makes the two fusion-natural word charts
commute before the surrounding occurrences are assembled. -/
def routedDisplayedPointEquiv (q : Occurrence C H) :
    (Σ c : (leftSlot C q).Cells,
      BinaryCarrierProfileTransport.mixturePoints ((leftSlot C q).color c)) ≃
    (Σ c : (rightSlot C hblocks htarget q).Cells,
      BinaryCarrierProfileTransport.mixturePoints
        ((rightSlot C hblocks htarget q).color c)) :=
  (slotChart (subgroup C H) (residualSector C H) q).trans
    ((occurrenceLocalPointEquiv C hblocks htarget q).trans
      (slotChart (subgroup C K) (residualSector C K)
        (eI C hblocks htarget q)).symm)

/-- On a proper route, equality of the retained mixed record says that the
displayed-point transport is the literal cast between the same fixed carrier
slot.  This includes the four-cell nonabelian `16T1086` carrier. -/
private theorem routedDisplayedPointEquiv_eq_of_proper
    (q : Occurrence C H) (e : Exceptional)
    (he : properKindAt (subgroup C H) (residualSector C H) q.1 = some e) :
    routedDisplayedPointEquiv C hblocks htarget q =
      displayedPointEquivOfEq (properSlotEq C hblocks htarget q e he) := by
  have heK : properKindAt (subgroup C K) (residualSector C K)
      (eI C hblocks htarget q).1 = some e := by
    rw [properKindAt_occurrenceEquiv C hblocks htarget q]
    exact he
  have hrecord :
      BinaryS16CanonicalMixedBlockTable.recordAt
          (subgroup C K) (residualSector C K) (eI C hblocks htarget q).1 =
        BinaryS16CanonicalMixedBlockTable.recordAt
          (subgroup C H) (residualSector C H) q.1 := by
    simpa [eI] using
      (BinaryS16SourceOrbitRecordStatus.sourceOrbitEquiv_recordAt
        C hblocks htarget q.1)
  generalize hpH : BinaryS16DirectCertifiedOrbitProfile.profile
      (subgroup C H) (residualSector C H) q.1 = CH at he hrecord ⊢
  generalize hpK : BinaryS16DirectCertifiedOrbitProfile.profile
      (subgroup C K) (residualSector C K)
        (eI C hblocks htarget q).1 = CK at heK hrecord ⊢
  cases CH <;> cases CK <;>
    simp [properKindAt_eq_certificateProperKind, hpH,
      hpK,
      certificateProperKind, degreeEightProperKind,
      degreeSixteenProperKind,
      BinaryS16CanonicalMixedBlockTable.recordAt,
      BinaryS16CanonicalMixedBlockTable.recordOfCertificate] at he heK hrecord ⊢
  case carrier8.carrier8 W_H hpoint_H R_H W_K hpoint_K R_K =>
    cases R_H <;> cases R_K <;>
      simp [BinaryCarrierS16TaggedPositiveRoutes.DegreeEightRoute.tag,
        degreeEightProperKind] at he hrecord ⊢
    all_goals
      subst e
      apply Equiv.ext
      intro z
      apply (slotChart (subgroup C K) (residualSector C K)
        (eI C hblocks htarget q)).injective
      simp only [routedDisplayedPointEquiv, Equiv.trans_apply,
        Equiv.apply_symm_apply]
      apply ((data (subgroup C K) (residualSector C K)).localChart
        (eI C hblocks htarget q).1 (eI C hblocks htarget q).2).injective
      apply Subtype.ext
      rw [occurrenceLocalPointEquiv_chart C hblocks htarget q]
      rw [BinaryS16JointAxisRouting.localChart_eq_transportedModelChart
          (subgroup C H) (residualSector C H) q,
        BinaryS16JointAxisRouting.localChart_eq_transportedModelChart
          (subgroup C K) (residualSector C K) (eI C hblocks htarget q)]
      rw [BinaryS16JointAxisRouting.exactOrbitChart_transport_point_coe,
        BinaryS16JointAxisRouting.exactOrbitChart_transport_point_coe]
      rw [← Equiv.trans_apply, ← Equiv.trans_apply]
      rw [slotChart_trans_localChart_eq_carrier8
          (subgroup C H) (residualSector C H) q _ _ _ hpH,
        slotChart_trans_localChart_eq_carrier8
          (subgroup C K) (residualSector C K)
            (eI C hblocks htarget q) _ _ _ hpK]
      let hrouteH := routeSlot_eq_of_profile
        (subgroup C H) (residualSector C H) q _ hpH
      let hrouteK := routeSlot_eq_of_profile
        (subgroup C K) (residualSector C K) (eI C hblocks htarget q) _ hpK
      let zH := routedDisplayedPointsCast hrouteH z
      let zK := routedDisplayedPointsCast hrouteK
        (displayedPointEquivOfEq (properSlotEq C hblocks htarget q _ he) z)
      have hz : zK = zH := by
        change displayedPointEquivOfEq hrouteK
            (displayedPointEquivOfEq
              (properSlotEq C hblocks htarget q _ he) z) =
          displayedPointEquivOfEq hrouteH z
        rw [displayedPointEquivOfEq_comp]
        rw [show (properSlotEq C hblocks htarget q _ he).trans hrouteK =
          hrouteH from Subsingleton.elim _ _]
        rfl
      have hz' : routedDisplayedPointsCast hrouteK
          (displayedPointEquivOfEq
            (properSlotEq C hblocks htarget q _ he) z) =
          routedDisplayedPointsCast hrouteH z := hz
      simp only [Equiv.trans_apply]
      rw [hz']
      let y : Fin 8 := Equiv.uniqueSigma (fun _ : Fin 1 => Fin 8) zH
      simp only [leftSlot, rightSlot, eI, routeSlot,
        BinaryS16JointAxisRouting.axisRouting,
        BinaryS16JointAxisRouting.routeCertificate,
        BinaryS16JointOrbitData.data,
        BinaryS16JointOrbitData.localModel,
        BinaryS16JointOrbitData.certificateLocalModel,
        Equiv.trans_apply, id_eq,
        BinaryCarrierS16TaggedPositiveRoutes.DegreeEightRoute.displayedPointEquiv,
        BinaryCarrierS16TaggedPositiveRoutes.DegreeEightRoute.changedBlock,
        BinaryCarrierS16TaggedPositiveRoutes.DegreeEightRoute.sourcePointEquiv,
        slotChart, properSlotEq, displayedPointEquivOfEq,
        hpH, hpK, hrouteH, hrouteK, zH, zK, hz, y]
      change
        ((((BinaryS16JointOrbitData.ExactOrbitChart.transport
          (subgroup C H) hpoint_H
          ⟨FusionActualOrbitCharts.orbitEquiv
              (subgroup C H) W_H.point W_H.orbit_card,
            BinaryS16JointOrbitData.witnessEight_image_eq
              (subgroup C H) W_H⟩).pointEquiv
            (((Equiv.uniqueSigma (fun _ : Fin 1 => Fin 8)).trans _)
              (routedDisplayedPointsCast hrouteH z)) : q.1.orbit) :
          Fin (2 * N))) =
        ((((BinaryS16JointOrbitData.ExactOrbitChart.transport
          (subgroup C K) hpoint_K
          ⟨FusionActualOrbitCharts.orbitEquiv
              (subgroup C K) W_K.point W_K.orbit_card,
            BinaryS16JointOrbitData.witnessEight_image_eq
              (subgroup C K) W_K⟩).pointEquiv
            (((Equiv.uniqueSigma (fun _ : Fin 1 => Fin 8)).trans _)
              (routedDisplayedPointsCast hrouteH z)) :
              (eI C hblocks htarget q).1.orbit) : Fin (2 * N)))
      rw [BinaryS16JointAxisRouting.exactOrbitChart_transport_point_coe,
        BinaryS16JointAxisRouting.exactOrbitChart_transport_point_coe]
      simpa [y, Equiv.trans_apply] using (congrFun hrecord.2 y).symm

  case carrier16.carrier16 W_H hpoint_H R_H W_K hpoint_K R_K =>
    cases R_H <;> cases R_K <;>
      simp [BinaryCarrierS16TaggedPositiveRoutes.DegreeSixteenRoute.tag,
        degreeSixteenProperKind] at he hrecord ⊢
    all_goals
      subst e
      apply Equiv.ext
      intro z
      apply (slotChart (subgroup C K) (residualSector C K)
        (eI C hblocks htarget q)).injective
      simp only [routedDisplayedPointEquiv, Equiv.trans_apply,
        Equiv.apply_symm_apply]
      apply ((data (subgroup C K) (residualSector C K)).localChart
        (eI C hblocks htarget q).1 (eI C hblocks htarget q).2).injective
      apply Subtype.ext
      rw [occurrenceLocalPointEquiv_chart C hblocks htarget q]
      rw [BinaryS16JointAxisRouting.localChart_eq_transportedModelChart
          (subgroup C H) (residualSector C H) q,
        BinaryS16JointAxisRouting.localChart_eq_transportedModelChart
          (subgroup C K) (residualSector C K) (eI C hblocks htarget q)]
      rw [BinaryS16JointAxisRouting.exactOrbitChart_transport_point_coe,
        BinaryS16JointAxisRouting.exactOrbitChart_transport_point_coe]
      rw [← Equiv.trans_apply, ← Equiv.trans_apply]
      rw [slotChart_trans_localChart_eq_carrier16
          (subgroup C H) (residualSector C H) q _ _ _ hpH,
        slotChart_trans_localChart_eq_carrier16
          (subgroup C K) (residualSector C K)
            (eI C hblocks htarget q) _ _ _ hpK]
      let hrouteH := routeSlot_eq_of_profile
        (subgroup C H) (residualSector C H) q _ hpH
      let hrouteK := routeSlot_eq_of_profile
        (subgroup C K) (residualSector C K) (eI C hblocks htarget q) _ hpK
      let zH := routedDisplayedPointsCast hrouteH z
      let zK := routedDisplayedPointsCast hrouteK
        (displayedPointEquivOfEq (properSlotEq C hblocks htarget q _ he) z)
      have hz : zK = zH := by
        change displayedPointEquivOfEq hrouteK
            (displayedPointEquivOfEq
              (properSlotEq C hblocks htarget q _ he) z) =
          displayedPointEquivOfEq hrouteH z
        rw [displayedPointEquivOfEq_comp]
        rw [show (properSlotEq C hblocks htarget q _ he).trans hrouteK =
          hrouteH from Subsingleton.elim _ _]
        rfl
      have hz' : routedDisplayedPointsCast hrouteK
          (displayedPointEquivOfEq
            (properSlotEq C hblocks htarget q _ he) z) =
          routedDisplayedPointsCast hrouteH z := hz
      simp only [Equiv.trans_apply]
      rw [hz']
      let y : Fin 16 :=
        ((BinaryCarrierFusionNaturalPointChart.profilePointEquivOccurrencePoint
          BinaryExceptional16PhysicalProfile.ExactProfile.pointFamily
          BinaryExceptional16PhysicalProfile.ExactProfile.multiplicity).symm.trans
            BinaryExceptional16PhysicalProfile.ExactProfile.chart) zH
      simp only [leftSlot, rightSlot, eI, routeSlot,
        BinaryS16JointAxisRouting.axisRouting,
        BinaryS16JointAxisRouting.routeCertificate,
        BinaryS16JointOrbitData.data,
        BinaryS16JointOrbitData.localModel,
        BinaryS16JointOrbitData.certificateLocalModel,
        Equiv.trans_apply, id_eq,
        BinaryCarrierS16TaggedPositiveRoutes.DegreeSixteenRoute.displayedPointEquiv,
        BinaryCarrierS16TaggedPositiveRoutes.DegreeSixteenRoute.changedBlock,
        BinaryCarrierS16TaggedPositiveRoutes.DegreeSixteenRoute.sourcePointEquiv,
        slotChart, properSlotEq, displayedPointEquivOfEq,
        hpH, hpK, hrouteH, hrouteK, zH, zK, hz, y]
      change
        ((((BinaryS16JointOrbitData.ExactOrbitChart.transport
          (subgroup C H) hpoint_H
          ⟨FusionActualOrbitCharts.orbitEquiv
              (subgroup C H) W_H.point W_H.orbit_card,
            BinaryS16JointOrbitData.witnessSixteen_image_eq
              (subgroup C H) W_H⟩).pointEquiv
            (((((BinaryCarrierFusionNaturalPointChart.profilePointEquivOccurrencePoint
                  BinaryExceptional16PhysicalProfile.ExactProfile.pointFamily
                  BinaryExceptional16PhysicalProfile.ExactProfile.multiplicity).symm.trans
                BinaryExceptional16PhysicalProfile.ExactProfile.chart).trans _))
              (routedDisplayedPointsCast hrouteH z)) : q.1.orbit) :
          Fin (2 * N))) =
        ((((BinaryS16JointOrbitData.ExactOrbitChart.transport
          (subgroup C K) hpoint_K
          ⟨FusionActualOrbitCharts.orbitEquiv
              (subgroup C K) W_K.point W_K.orbit_card,
            BinaryS16JointOrbitData.witnessSixteen_image_eq
              (subgroup C K) W_K⟩).pointEquiv
            (((((BinaryCarrierFusionNaturalPointChart.profilePointEquivOccurrencePoint
                  BinaryExceptional16PhysicalProfile.ExactProfile.pointFamily
                  BinaryExceptional16PhysicalProfile.ExactProfile.multiplicity).symm.trans
                BinaryExceptional16PhysicalProfile.ExactProfile.chart).trans _))
              (routedDisplayedPointsCast hrouteH z)) :
              (eI C hblocks htarget q).1.orbit) : Fin (2 * N)))
      rw [BinaryS16JointAxisRouting.exactOrbitChart_transport_point_coe,
        BinaryS16JointAxisRouting.exactOrbitChart_transport_point_coe]
      simpa [y, Equiv.trans_apply] using (congrFun hrecord.2 y).symm

/-- Pointwise form of the proper-route chart comparison.  It is the exact
local square used below to reflect source elements from their faithful
actions on the fixed exceptional displayed points. -/
private theorem occurrenceLocalPointEquiv_slotChart_of_proper
    (q : Occurrence C H) (e : Exceptional)
    (he : properKindAt (subgroup C H) (residualSector C H) q.1 = some e)
    (z : Σ c : (leftSlot C q).Cells,
      BinaryCarrierProfileTransport.mixturePoints ((leftSlot C q).color c)) :
    occurrenceLocalPointEquiv C hblocks htarget q
        (slotChart (subgroup C H) (residualSector C H) q z) =
      slotChart (subgroup C K) (residualSector C K)
        (eI C hblocks htarget q)
        (displayedPointEquivOfEq
          (properSlotEq C hblocks htarget q e he) z) := by
  have h := congrArg (fun E => E z)
    (routedDisplayedPointEquiv_eq_of_proper C hblocks htarget q e he)
  simpa only [routedDisplayedPointEquiv, Equiv.trans_apply,
    Equiv.apply_symm_apply] using congrArg
      (slotChart (subgroup C K) (residualSector C K)
        (eI C hblocks htarget q)) h

/-- Source transport used by the indexed word reflection.  Proper routes use
literal fixed-slot transport.  Identity routes use the actual local-action
conjugacy, expressed in the two routed source coordinates. -/
def routedSourceEquiv (q : Occurrence C H) :
    (leftSlot C q).Source ≃* (rightSlot C hblocks htarget q).Source :=
  ((BinaryS16JointAxisRouting.axisRouting
      (subgroup C H) (residualSector C H) q).axisSlot.sourceEquiv).symm |>.trans
    ((actionEquiv C hblocks htarget q).trans
      (BinaryS16JointAxisRouting.axisRouting
        (subgroup C K) (residualSector C K)
        (eI C hblocks htarget q)).axisSlot.sourceEquiv)

/-- On a matched proper route, the source isomorphism obtained by following
the two local-action charts is exactly literal transport of the fixed
exceptional slot.  Faithfulness of the fixed displayed action is what rules
out a hidden automorphism of the proper source, including for 16T1086. -/
private theorem routedSourceEquiv_eq_of_proper
    (q : Occurrence C H) (e : Exceptional)
    (he : properKindAt (subgroup C H) (residualSector C H) q.1 = some e) :
    routedSourceEquiv C hblocks htarget q =
      sourceEquivOfEq (properSlotEq C hblocks htarget q e he) := by
  let RH := BinaryS16JointAxisRouting.axisRouting
    (subgroup C H) (residualSector C H) q
  let RK := BinaryS16JointAxisRouting.axisRouting
    (subgroup C K) (residualSector C K) (eI C hblocks htarget q)
  let hS := (matched_proper_slots C hblocks htarget q e he).1
  let hT := (matched_proper_slots C hblocks htarget q e he).2
  let hST := properSlotEq C hblocks htarget q e he
  have heK : properKindAt (subgroup C K) (residualSector C K)
      (eI C hblocks htarget q).1 = some e := by
    rw [properKindAt_occurrenceEquiv C hblocks htarget q]
    exact he
  apply MulEquiv.ext
  intro u
  apply transportedDisplayedAction_injective e hT
  apply Equiv.ext
  intro zK
  obtain ⟨z,rfl⟩ := (displayedPointEquivOfEq hST).surjective zK
  change transportedDisplayedAction e hT
      (RK.axisSlot.sourceEquiv
        (actionEquiv C hblocks htarget q (RH.axisSlot.sourceEquiv.symm u)))
      (displayedPointEquivOfEq hST z) =
    transportedDisplayedAction e hT (sourceEquivOfEq hST u)
      (displayedPointEquivOfEq hST z)
  rw [transportedDisplayedAction_natural e hS hT hST u z]
  apply (slotChart (subgroup C K) (residualSector C K)
    (eI C hblocks htarget q)).injective
  rw [axisRouting_proper_action
    (subgroup C K) (residualSector C K) (eI C hblocks htarget q)
      e heK hT
      (actionEquiv C hblocks htarget q (RH.axisSlot.sourceEquiv.symm u))
      (displayedPointEquivOfEq hST z)]
  rw [← occurrenceLocalPointEquiv_slotChart_of_proper
    C hblocks htarget q e he
      (transportedDisplayedAction e hS u z)]
  rw [show u = RH.axisSlot.sourceEquiv
      (RH.axisSlot.sourceEquiv.symm u) from
        (RH.axisSlot.sourceEquiv.apply_symm_apply u).symm]
  rw [axisRouting_proper_action
    (subgroup C H) (residualSector C H) q e he hS
      (RH.axisSlot.sourceEquiv.symm u) z]
  rw [← localActionEquiv_apply_point C hblocks htarget
    (occurrenceLocalPointEquiv_action C hblocks htarget)
      q (RH.axisSlot.sourceEquiv.symm u)
      (slotChart (subgroup C H) (residualSector C H) q z)]
  rw [occurrenceLocalPointEquiv_slotChart_of_proper
    C hblocks htarget q e he z]
  simp [actionEquiv, hST]

/-- Replacement-carrier transport matched to `routedSourceEquiv`. -/
def routedCarrierEquiv (q : Occurrence C H) :
    carriers (fun r => leftSlot C r) q ≃*
      carriers (fun r => rightSlot C hblocks htarget r) q := by
  by_cases he : properKindAt
      (subgroup C H) (residualSector C H) q.1 = none
  · let P := matched_identityPresentations C hblocks htarget q he
    exact carrierEquiv P.1 P.2 (routedSourceEquiv C hblocks htarget q)
  · have hs : (properKindAt
        (subgroup C H) (residualSector C H) q.1).isSome :=
      Option.isSome_iff_ne_none.mpr he
    let e := (properKindAt
      (subgroup C H) (residualSector C H) q.1).get hs
    have heq : properKindAt (subgroup C H) (residualSector C H) q.1 = some e :=
      Option.eq_some_iff_get_eq.mpr ⟨hs,rfl⟩
    exact carrierEquivOfEq (properSlotEq C hblocks htarget q e heq)

/-- Proper matched routes transport the replacement carrier by the same
literal bundled-slot equality as their displayed points. -/
private theorem routedCarrierEquiv_eq_of_proper
    (q : Occurrence C H) (e : Exceptional)
    (he : properKindAt (subgroup C H) (residualSector C H) q.1 = some e) :
    routedCarrierEquiv C hblocks htarget q =
      carrierEquivOfEq (properSlotEq C hblocks htarget q e he) := by
  have hs : (properKindAt
      (subgroup C H) (residualSector C H) q.1).isSome := by
    rw [he]
    rfl
  simp [routedCarrierEquiv, he, hs]

/-- On an exposed quotient-identity cell, the generic displayed-carrier
action of a constant section is its standard one-cell source action. -/
private theorem displayedCarrierAction_section
    {S : Slot} (P : IdentityPresentation S) (u : S.Source)
    (z : Σ c : S.Cells,
      BinaryCarrierProfileTransport.mixturePoints (S.color c)) :
    displayedCarrierAction S (carrierSection P u) z =
      identitySlotAction P u z := by
  rcases P with ⟨g,M,hM,hS⟩
  subst S
  rfl

/-- Every local carrier action commutes with the exact displayed-point
transport.  Identity cells use their reversible one-cell evaluation and the
canonical local-action conjugacy; proper cells use literal fixed-slot casts. -/
private theorem routedCarrierAction_natural
    (q : Occurrence C H)
    (p : carriers (fun r => leftSlot C r) q)
    (z : Σ c : (leftSlot C q).Cells,
      BinaryCarrierProfileTransport.mixturePoints ((leftSlot C q).color c)) :
    routedDisplayedPointEquiv C hblocks htarget q
        (displayedCarrierAction (leftSlot C q) p z) =
      displayedCarrierAction (rightSlot C hblocks htarget q)
        (routedCarrierEquiv C hblocks htarget q p)
        (routedDisplayedPointEquiv C hblocks htarget q z) := by
  by_cases he : properKindAt
      (subgroup C H) (residualSector C H) q.1 = none
  · let P := matched_identityPresentations C hblocks htarget q he
    let RH := BinaryS16JointAxisRouting.axisRouting
      (subgroup C H) (residualSector C H) q
    let RK := BinaryS16JointAxisRouting.axisRouting
      (subgroup C K) (residualSector C K) (eI C hblocks htarget q)
    let u : LocalAction C H q :=
      RH.axisSlot.sourceEquiv.symm (carrierEval P.1 p)
    have huH : RH.axisSlot.sourceEquiv u = carrierEval P.1 p := by
      exact RH.axisSlot.sourceEquiv.apply_symm_apply _
    have huK : RK.axisSlot.sourceEquiv
        (actionEquiv C hblocks htarget q u) =
        carrierEval P.2 (routedCarrierEquiv C hblocks htarget q p) := by
      change
        RK.axisSlot.sourceEquiv (actionEquiv C hblocks htarget q u) = _
      rw [← show routedSourceEquiv C hblocks htarget q
          (RH.axisSlot.sourceEquiv u) =
          RK.axisSlot.sourceEquiv (actionEquiv C hblocks htarget q u) by
        simp [routedSourceEquiv, RH, RK]]
      rw [huH]
      simpa [routedCarrierEquiv, he, P] using
        (carrierEval_carrierEquiv P.1 P.2
          (routedSourceEquiv C hblocks htarget q) p).symm
    have hleft : displayedCarrierAction (leftSlot C q) p z =
        identitySlotAction P.1 (RH.axisSlot.sourceEquiv u) z := by
      calc
        displayedCarrierAction (leftSlot C q) p z =
            displayedCarrierAction (leftSlot C q)
              (carrierSection P.1 (carrierEval P.1 p)) z := by
                rw [carrierSection_eval]
        _ = identitySlotAction P.1 (carrierEval P.1 p) z :=
          displayedCarrierAction_section P.1 _ z
        _ = identitySlotAction P.1 (RH.axisSlot.sourceEquiv u) z := by
          rw [huH]
    have hright (w : Σ c : (rightSlot C hblocks htarget q).Cells,
        BinaryCarrierProfileTransport.mixturePoints
          ((rightSlot C hblocks htarget q).color c)) :
        displayedCarrierAction (rightSlot C hblocks htarget q)
            (routedCarrierEquiv C hblocks htarget q p) w =
          identitySlotAction P.2
            (RK.axisSlot.sourceEquiv
              (actionEquiv C hblocks htarget q u)) w := by
      calc
        displayedCarrierAction (rightSlot C hblocks htarget q)
            (routedCarrierEquiv C hblocks htarget q p) w =
            displayedCarrierAction (rightSlot C hblocks htarget q)
              (carrierSection P.2
                (carrierEval P.2
                  (routedCarrierEquiv C hblocks htarget q p))) w := by
                    rw [carrierSection_eval]
        _ = identitySlotAction P.2
            (carrierEval P.2
              (routedCarrierEquiv C hblocks htarget q p)) w :=
          displayedCarrierAction_section P.2 _ w
        _ = identitySlotAction P.2
            (RK.axisSlot.sourceEquiv
              (actionEquiv C hblocks htarget q u)) w := by rw [huK]
    apply (slotChart (subgroup C K) (residualSector C K)
      (eI C hblocks htarget q)).injective
    rw [hleft, hright]
    calc
      slotChart (subgroup C K) (residualSector C K)
          (eI C hblocks htarget q)
          (routedDisplayedPointEquiv C hblocks htarget q
            (identitySlotAction P.1 (RH.axisSlot.sourceEquiv u) z)) =
          occurrenceLocalPointEquiv C hblocks htarget q
            (slotChart (subgroup C H) (residualSector C H) q
              (identitySlotAction P.1 (RH.axisSlot.sourceEquiv u) z)) := by
        simp [routedDisplayedPointEquiv]
      _ = occurrenceLocalPointEquiv C hblocks htarget q
          ((u : Equiv.Perm _) (slotChart
            (subgroup C H) (residualSector C H) q z)) := by
        apply congrArg (occurrenceLocalPointEquiv C hblocks htarget q)
        simpa [P, RH] using
          (axisRouting_identity_action
            (subgroup C H) (residualSector C H) q he u
            (slotChart (subgroup C H) (residualSector C H) q z))
      _ = ((actionEquiv C hblocks htarget q u :
            LocalAction C K (eI C hblocks htarget q)) : Equiv.Perm _)
          (occurrenceLocalPointEquiv C hblocks htarget q
            (slotChart (subgroup C H) (residualSector C H) q z)) := by
        simpa [actionEquiv] using
          (localActionEquiv_apply_point C hblocks htarget
            (occurrenceLocalPointEquiv_action C hblocks htarget)
            q u (slotChart (subgroup C H) (residualSector C H) q z)).symm
      _ = slotChart (subgroup C K) (residualSector C K)
          (eI C hblocks htarget q)
          (identitySlotAction P.2
            (RK.axisSlot.sourceEquiv
              (actionEquiv C hblocks htarget q u))
            (routedDisplayedPointEquiv C hblocks htarget q z)) := by
        have heK : properKindAt (subgroup C K) (residualSector C K)
            (eI C hblocks htarget q).1 = none := by
          rw [properKindAt_occurrenceEquiv C hblocks htarget q]
          exact he
        have hK := axisRouting_identity_action
          (subgroup C K) (residualSector C K)
          (eI C hblocks htarget q) heK
          (actionEquiv C hblocks htarget q u)
          (slotChart (subgroup C K) (residualSector C K)
            (eI C hblocks htarget q)
            (routedDisplayedPointEquiv C hblocks htarget q z))
        rw [show occurrenceLocalPointEquiv C hblocks htarget q
              (slotChart (subgroup C H) (residualSector C H) q z) =
            slotChart (subgroup C K) (residualSector C K)
              (eI C hblocks htarget q)
              (routedDisplayedPointEquiv C hblocks htarget q z) by
          simp [routedDisplayedPointEquiv]]
        simpa [P, RK] using hK.symm
  · have hs : (properKindAt
        (subgroup C H) (residualSector C H) q.1).isSome :=
      Option.isSome_iff_ne_none.mpr he
    let e := (properKindAt
      (subgroup C H) (residualSector C H) q.1).get hs
    have heq : properKindAt (subgroup C H) (residualSector C H) q.1 = some e :=
      Option.eq_some_iff_get_eq.mpr ⟨hs,rfl⟩
    rw [routedDisplayedPointEquiv_eq_of_proper C hblocks htarget q e heq,
      routedCarrierEquiv_eq_of_proper C hblocks htarget q e heq]
    exact displayedCarrierAction_cast
      (properSlotEq C hblocks htarget q e heq) p z

/-- Reindex the complete sigma of displayed carrier points. -/
def routedLiteralPointEquiv :
    LiteralPoints (slot C H) ≃ LiteralPoints (slot C K) :=
  Equiv.sigmaCongr (eI C hblocks htarget)
    (routedDisplayedPointEquiv C hblocks htarget)

/-- The product carrier action commutes with the assembled displayed-point
reindexing. -/
theorem literalAction_natural
    (p : ∀ q, carriers (slot C H) q) :
    (routedLiteralPointEquiv C hblocks htarget).permCongr
        (literalAction (slot C H) p) =
      literalAction (slot C K)
        (indexedProductEquiv
          (U₁ := fun q => carriers (slot C H) q)
          (U₂ := fun q => carriers (slot C K) q)
          (eI C hblocks htarget)
          (routedCarrierEquiv C hblocks htarget) p) := by
  apply Equiv.ext
  intro y
  obtain ⟨z,rfl⟩ := (routedLiteralPointEquiv C hblocks htarget).surjective y
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rcases z with ⟨q,z⟩
  change
    (⟨eI C hblocks htarget q,
      routedDisplayedPointEquiv C hblocks htarget q
        (displayedCarrierAction (leftSlot C q) (p q) z)⟩ :
        LiteralPoints (slot C K)) =
      (⟨eI C hblocks htarget q,
        displayedCarrierAction (rightSlot C hblocks htarget q)
          ((indexedProductEquiv
            (U₁ := fun r => carriers (slot C H) r)
            (U₂ := fun r => carriers (slot C K) r)
            (eI C hblocks htarget)
            (routedCarrierEquiv C hblocks htarget) p)
              (eI C hblocks htarget q))
          (routedDisplayedPointEquiv C hblocks htarget q z)⟩ :
        LiteralPoints (slot C K))
  rw [indexedProductEquiv_apply]
  exact Sigma.ext rfl (heq_of_eq
    (routedCarrierAction_natural C hblocks htarget q (p q) z))

/-- Every matched route supplies the kernel-first quotient square expected by
the indexed reflection theorem. -/
def routedNaturalizer (q : Occurrence C H)
    (hkernel :
      (betas (fun r => leftSlot C r) q).ker.map
          (routedCarrierEquiv C hblocks htarget q).toMonoidHom =
        (betas (fun r => rightSlot C hblocks htarget r) q).ker) :
    QuotientSquare
      (alphas (fun r => leftSlot C r) q)
      (alphas (fun r => rightSlot C hblocks htarget r) q)
      (betas (fun r => leftSlot C r) q)
      (betas (fun r => rightSlot C hblocks htarget r) q)
      (routedSourceEquiv C hblocks htarget q)
      (routedCarrierEquiv C hblocks htarget q) := by
  by_cases he : properKindAt
      (subgroup C H) (residualSector C H) q.1 = none
  · let P := matched_identityPresentations C hblocks htarget q he
    simpa [routedCarrierEquiv, he] using
      (quotientSquare P.1 P.2
        (routedSourceEquiv C hblocks htarget q)
        (by simpa [routedCarrierEquiv, he] using hkernel))
  · have hs : (properKindAt
        (subgroup C H) (residualSector C H) q.1).isSome :=
      Option.isSome_iff_ne_none.mpr he
    let e := (properKindAt
      (subgroup C H) (residualSector C H) q.1).get hs
    have heq : properKindAt (subgroup C H) (residualSector C H) q.1 = some e :=
      Option.eq_some_iff_get_eq.mpr ⟨hs,rfl⟩
    let hslot := properSlotEq C hblocks htarget q e heq
    rw [routedSourceEquiv_eq_of_proper C hblocks htarget q e heq]
    simpa [routedCarrierEquiv, he, hs, e, hslot] using
      (quotientSquareOfEq hslot)

/-! ## Reassembling the indexed source word -/

/-- The routed source comparison was chosen so that the square from the
literal local action to the two route coordinates commutes on the nose. -/
private theorem routedSourceEquiv_square (q : Occurrence C H)
    (u : LocalAction C H q) :
    routedSourceEquiv C hblocks htarget q
        ((BinaryS16JointAxisRouting.axisRouting
          (subgroup C H) (residualSector C H) q).axisSlot.sourceEquiv u) =
      (BinaryS16JointAxisRouting.axisRouting
        (subgroup C K) (residualSector C K)
          (eI C hblocks htarget q)).axisSlot.sourceEquiv
        (actionEquiv C hblocks htarget q u) := by
  simp [routedSourceEquiv]

/-- Simultaneous route transport is exactly the canonical flat source
transport, followed by the right route coordinates.  This is the reversible
binary-source reindexing identity; no route or chart is counted as a mark. -/
private theorem routedSourceProductEquiv_eq :
    (BinaryCarrierRoutedWordClosure.sourceProductEquiv
        (fun q : Occurrence C H => LocalAction C H q)
        (fun q => CanonicalOrbitWord.axis
          (Points (subgroup C H) (residualSector C H))
          (action (subgroup C H) (residualSector C H))
          (subgroup C H)
          (data (subgroup C H) (residualSector C H)) q)
        (fun q => (BinaryS16JointAxisRouting.axisRouting
          (subgroup C H) (residualSector C H) q).axisSlot)).trans
      (indexedProductEquiv
        (U₁ := fun q => (leftSlot C q).Source)
        (U₂ := fun q => (slot C K q).Source)
        (eI C hblocks htarget)
        (routedSourceEquiv C hblocks htarget)) =
    (canonicalFlatGroupEquiv C hblocks htarget).trans
      (BinaryCarrierRoutedWordClosure.sourceProductEquiv
        (fun q : Occurrence C K => LocalAction C K q)
        (fun q => CanonicalOrbitWord.axis
          (Points (subgroup C K) (residualSector C K))
          (action (subgroup C K) (residualSector C K))
          (subgroup C K)
          (data (subgroup C K) (residualSector C K)) q)
        (fun q => (BinaryS16JointAxisRouting.axisRouting
          (subgroup C K) (residualSector C K) q).axisSlot)) := by
  apply MulEquiv.ext
  intro x
  funext j
  obtain ⟨q,rfl⟩ := (eI C hblocks htarget).surjective j
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply,
    indexedProductEquiv_apply]
  rw [BinaryCarrierRoutedWordClosure.sourceProductEquiv_apply,
    BinaryCarrierRoutedWordClosure.sourceProductEquiv_apply]
  rw [show canonicalFlatGroupEquiv C hblocks htarget =
      flatGroupEquiv C hblocks htarget
        (occurrenceLocalPointEquiv_action C hblocks htarget) from rfl]
  rw [BinaryS16CommonSourceTransport.flatGroupEquiv_apply]
  exact routedSourceEquiv_square C hblocks htarget q (x q)

/-- Equality of the routed word sources therefore recovers equality of the
canonical flat sources. -/
theorem canonicalFlatSource_eq_of_wordSource_eq
    (hword :
      (wordSource C H).1.map
          (indexedProductEquiv
            (U₁ := fun q => (leftSlot C q).Source)
            (U₂ := fun q => (slot C K q).Source)
            (eI C hblocks htarget)
            (routedSourceEquiv C hblocks htarget)).toMonoidHom =
        (wordSource C K).1) :
    (CanonicalOrbitWord.flatSource
        (Points (subgroup C H) (residualSector C H))
        (action (subgroup C H) (residualSector C H))
        (subgroup C H)
        (data (subgroup C H) (residualSector C H))).map
          (canonicalFlatGroupEquiv C hblocks htarget).toMonoidHom =
      CanonicalOrbitWord.flatSource
        (Points (subgroup C K) (residualSector C K))
        (action (subgroup C K) (residualSector C K))
        (subgroup C K)
        (data (subgroup C K) (residualSector C K)) := by
  let EH := BinaryCarrierRoutedWordClosure.sourceProductEquiv
    (fun q : Occurrence C H => LocalAction C H q)
    (fun q => CanonicalOrbitWord.axis
      (Points (subgroup C H) (residualSector C H))
      (action (subgroup C H) (residualSector C H))
      (subgroup C H) (data (subgroup C H) (residualSector C H)) q)
    (fun q => (BinaryS16JointAxisRouting.axisRouting
      (subgroup C H) (residualSector C H) q).axisSlot)
  let EK := BinaryCarrierRoutedWordClosure.sourceProductEquiv
    (fun q : Occurrence C K => LocalAction C K q)
    (fun q => CanonicalOrbitWord.axis
      (Points (subgroup C K) (residualSector C K))
      (action (subgroup C K) (residualSector C K))
      (subgroup C K) (data (subgroup C K) (residualSector C K)) q)
    (fun q => (BinaryS16JointAxisRouting.axisRouting
      (subgroup C K) (residualSector C K) q).axisSlot)
  let E := indexedProductEquiv
    (U₁ := fun q => (leftSlot C q).Source)
    (U₂ := fun q => (slot C K q).Source)
    (eI C hblocks htarget)
    (routedSourceEquiv C hblocks htarget)
  have hroute : EH.trans E =
      (canonicalFlatGroupEquiv C hblocks htarget).trans EK := by
    exact routedSourceProductEquiv_eq C hblocks htarget
  have hhom : E.toMonoidHom.comp EH.toMonoidHom =
      EK.toMonoidHom.comp
        (canonicalFlatGroupEquiv C hblocks htarget).toMonoidHom := by
    exact congrArg MulEquiv.toMonoidHom hroute
  have hword' :
      ((CanonicalOrbitWord.flatSource
        (Points (subgroup C H) (residualSector C H))
        (action (subgroup C H) (residualSector C H))
        (subgroup C H)
        (data (subgroup C H) (residualSector C H))).map EH.toMonoidHom).map
          E.toMonoidHom =
      (CanonicalOrbitWord.flatSource
        (Points (subgroup C K) (residualSector C K))
        (action (subgroup C K) (residualSector C K))
        (subgroup C K)
        (data (subgroup C K) (residualSector C K))).map EK.toMonoidHom := by
    simpa [wordSource, CanonicalOrbitWord.sourceAt,
      BinaryCarrierRoutedWordClosure.routedSource, EH, EK, E] using hword
  apply Subgroup.map_injective (f := EK.toMonoidHom) EK.injective
  rw [Subgroup.map_map]
  rw [← hhom]
  rw [← Subgroup.map_map]
  exact hword'

end Matched

end SymmetricSubgroupAsymptotics.BinaryS16FinalFibreReflection

end
