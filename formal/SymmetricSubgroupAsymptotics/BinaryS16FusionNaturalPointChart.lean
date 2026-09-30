import SymmetricSubgroupAsymptotics.BinaryCarrierS16TaggedRoutePointCharts
import SymmetricSubgroupAsymptotics.BinaryS16JointCertifiedWord

/-!
# The fusion-natural point chart of the joint S16 word

The joint certified word is indexed by the literal orbits of the original
subgroup.  Its positive route packages retain an exact chart from the points
displayed by the route back to the source action, while its critical routes
display one identity cell.  These local charts assemble to one chart from the
completed carrier mixture onto the original ambient labels.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16FusionNaturalPointChart

open SymmetricSubgroupAsymptotics
open BinaryCarrierCanonicalCertifiedWord
open BinaryCarrierCellProfile
open BinaryCarrierFusionNaturalPointChart
open BinaryCarrierParameterProfiles
open BinaryCarrierProfileTransport
open BinaryCarrierS16TaggedPositiveRoutes
open BinaryCarrierWordClosure
open BinaryS16CanonicalCarrierProfile
open BinaryS16DirectCertifiedOrbitProfile

variable {N : ℕ}
variable (H : Subgroup (Equiv.Perm (Fin (2 * N))))
variable (hH : ResidualSector H)

abbrev Occurrence :=
  Σ o, Fin ((BinaryS16JointOrbitData.data H hH).multiplicity o)

abbrev routeSlot (q : Occurrence H hH) :=
  ((BinaryS16JointAxisRouting.axisRouting H hH q).axisSlot).slot

private abbrev RoutedDisplayedPoints (S : Slot.{0,0,0}) :=
  Σ c : S.Cells, mixturePoints (S.color c)

private def finOneSigma (A : Type) : (Σ _ : Fin 1, A) ≃ A where
  toFun z := z.2
  invFun x := ⟨0,x⟩
  left_inv := by
    rintro ⟨i,x⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  right_inv := fun _ => rfl

/-- Public name for the unique-cell point equivalence used by all critical
identity routes. -/
def oneCellPointEquiv (A : Type) : (Σ _ : Fin 1, A) ≃ A :=
  finOneSigma A

@[simp] theorem oneCellPointEquiv_apply (A : Type) (z : Σ _ : Fin 1, A) :
    oneCellPointEquiv A z = z.2 := rfl

@[simp] theorem oneCellPointEquiv_symm_apply (A : Type) (x : A) :
    (oneCellPointEquiv A).symm x = ⟨0,x⟩ := rfl

/-- `Equiv.uniqueSigma` does not change the second coordinate when the
dependent family is actually constant. -/
private theorem uniqueSigma_const_apply {A B : Type} [Unique A]
    (z : Σ _ : A, B) :
    Equiv.uniqueSigma (fun _ : A => B) z = z.2 := by
  rcases z with ⟨a,b⟩
  have ha : a = default := Unique.eq_default a
  cases ha
  rfl

/-- The point chart attached to an explicitly supplied certificate.  Both
the route and the local point type reduce by the same certificate case. -/
private def certificateSlotChart
    (q : Occurrence H hH) (C : OrbitCertificate H q.1)
    (hp : profile H hH q.1 = C) :
    RoutedDisplayedPoints
        (BinaryS16JointAxisRouting.routeCertificate
          H hH q C hp).axisSlot.slot ≃
      (BinaryS16JointOrbitData.certificateLocalModel H C).Points := by
  cases C with
  | c2 e he =>
      unfold BinaryS16JointAxisRouting.routeCertificate
      simp only
      unfold BinaryS16JointAxisRouting.criticalRouteC2
      simp
      change (Σ _ : Fin 1, criticalActionPoints .c2) ≃
        criticalActionPoints .c2
      exact finOneSigma _
  | v4 e he =>
      unfold BinaryS16JointAxisRouting.routeCertificate
      simp only
      unfold BinaryS16JointAxisRouting.criticalRouteV4
      simp
      change (Σ _ : Fin 1, criticalActionPoints .v4) ≃
        criticalActionPoints .v4
      exact finOneSigma _
  | d8 e he =>
      unfold BinaryS16JointAxisRouting.routeCertificate
      simp only
      unfold BinaryS16JointAxisRouting.criticalRouteD8
      simp
      change (Σ _ : Fin 1, criticalActionPoints .d8) ≃
        criticalActionPoints .d8
      exact finOneSigma _
  | e8 e he =>
      unfold BinaryS16JointAxisRouting.routeCertificate
      simp only
      unfold BinaryS16JointAxisRouting.criticalRouteE8
      simp
      change (Σ _ : Fin 1, criticalActionPoints .e8) ≃
        criticalActionPoints .e8
      exact finOneSigma _
  | cyclicFour W hpoint R =>
      unfold BinaryS16JointAxisRouting.routeCertificate
      simp only
      unfold BinaryS16JointAxisRouting.positiveRouteC4
      simp
      change RoutedDisplayedPoints R.certified.axisSlot.slot ≃ Fin 4
      exact R.displayedPointEquiv
  | carrier8 W hpoint R =>
      unfold BinaryS16JointAxisRouting.routeCertificate
      simp only
      unfold BinaryS16JointAxisRouting.positiveRouteC8
      simp
      change RoutedDisplayedPoints R.certified.axisSlot.slot ≃ Fin 8
      exact R.displayedPointEquiv
  | carrier16 W hpoint R =>
      unfold BinaryS16JointAxisRouting.routeCertificate
      simp only
      unfold BinaryS16JointAxisRouting.positiveRouteC16
      simp
      change RoutedDisplayedPoints R.certified.axisSlot.slot ≃ Fin 16
      exact R.displayedPointEquiv

/-- Public certificate-level form of the routed displayed-point chart.  This
lets semantic naturality be proved by induction on the same certificate,
without first transporting through the opaque selected profile. -/
def certificateSlotChartExact
    (q : Occurrence H hH) (C : OrbitCertificate H q.1)
    (hp : profile H hH q.1 = C) :
    RoutedDisplayedPoints
        (BinaryS16JointAxisRouting.routeCertificate
          H hH q C hp).axisSlot.slot ≃
      (BinaryS16JointOrbitData.certificateLocalModel H C).Points :=
  certificateSlotChart H hH q C hp

@[simp] theorem certificateSlotChartExact_c2
    (q : Occurrence H hH)
    (e : criticalActionPoints .c2 ≃ q.1.orbit)
    (he : relabelSubgroup e (criticalActionSubgroup .c2) =
      OrbitProfileFromOrbits.orbitImage H q.1)
    (hp : profile H hH q.1 = OrbitCertificate.c2 e he) :
    certificateSlotChartExact H hH q (OrbitCertificate.c2 e he) hp =
      oneCellPointEquiv (criticalActionPoints .c2) := rfl

@[simp] theorem certificateSlotChartExact_v4
    (q : Occurrence H hH)
    (e : criticalActionPoints .v4 ≃ q.1.orbit)
    (he : relabelSubgroup e (criticalActionSubgroup .v4) =
      OrbitProfileFromOrbits.orbitImage H q.1)
    (hp : profile H hH q.1 = OrbitCertificate.v4 e he) :
    certificateSlotChartExact H hH q (OrbitCertificate.v4 e he) hp =
      oneCellPointEquiv (criticalActionPoints .v4) := rfl

@[simp] theorem certificateSlotChartExact_d8
    (q : Occurrence H hH)
    (e : criticalActionPoints .d8 ≃ q.1.orbit)
    (he : relabelSubgroup e (criticalActionSubgroup .d8) =
      OrbitProfileFromOrbits.orbitImage H q.1)
    (hp : profile H hH q.1 = OrbitCertificate.d8 e he) :
    certificateSlotChartExact H hH q (OrbitCertificate.d8 e he) hp =
      oneCellPointEquiv (criticalActionPoints .d8) := rfl

@[simp] theorem certificateSlotChartExact_e8
    (q : Occurrence H hH)
    (e : criticalActionPoints .e8 ≃ q.1.orbit)
    (he : relabelSubgroup e (criticalActionSubgroup .e8) =
      OrbitProfileFromOrbits.orbitImage H q.1)
    (hp : profile H hH q.1 = OrbitCertificate.e8 e he) :
    certificateSlotChartExact H hH q (OrbitCertificate.e8 e he) hp =
      oneCellPointEquiv (criticalActionPoints .e8) := rfl

@[simp] theorem certificateSlotChartExact_cyclicFour
    (q : Occurrence H hH)
    (W : BinaryS16CanonicalCarrierProfile.SmallOrbitWitness 4 H)
    (hpoint : Quotient.mk'' W.point = q.1)
    (R : BinaryCarrierS16TaggedPositiveRoutes.DegreeFourRoute W)
    (hp : profile H hH q.1 = OrbitCertificate.cyclicFour W hpoint R) :
    certificateSlotChartExact H hH q
      (OrbitCertificate.cyclicFour W hpoint R) hp = R.displayedPointEquiv := rfl

@[simp] theorem certificateSlotChartExact_carrier8
    (q : Occurrence H hH)
    (W : BinaryDegreeEightNormalizerSaturatedDirect.OrbitWitness H)
    (hpoint : Quotient.mk'' W.point = q.1)
    (R : BinaryCarrierS16TaggedPositiveRoutes.DegreeEightRoute W.action W.axis)
    (hp : profile H hH q.1 = OrbitCertificate.carrier8 W hpoint R) :
    certificateSlotChartExact H hH q
      (OrbitCertificate.carrier8 W hpoint R) hp = R.displayedPointEquiv := rfl

@[simp] theorem certificateSlotChartExact_carrier16
    (q : Occurrence H hH)
    (W : BinaryDegree16PhysicalAnalyticClosure.OrbitWitness H)
    (hpoint : Quotient.mk'' W.point = q.1)
    (R : BinaryCarrierS16TaggedPositiveRoutes.DegreeSixteenRoute W.action W.axis)
    (hp : profile H hH q.1 = OrbitCertificate.carrier16 W hpoint R) :
    certificateSlotChartExact H hH q
      (OrbitCertificate.carrier16 W hpoint R) hp = R.displayedPointEquiv := rfl

/-- The displayed points of one routed occurrence, on the source labels of
the exact local action selected by the same orbit certificate. -/
def slotChart (q : Occurrence H hH) :
    (Σ c : (routeSlot H hH q).Cells,
      mixturePoints ((routeSlot H hH q).color c)) ≃
        BinaryS16JointOrbitData.Points H hH q.1 := by
  exact certificateSlotChart H hH q (profile H hH q.1) rfl

@[simp] theorem certificateSlotChartExact_selected
    (q : Occurrence H hH) :
    certificateSlotChartExact H hH q (profile H hH q.1) rfl =
      slotChart H hH q := rfl

/-- Replace the selected certificate by an equal explicit certificate at the
level of routed slots.  The slot itself is independent of the equality
witness, so ordinary equality induction suffices here. -/
theorem routeSlot_eq_of_profile
    (q : Occurrence H hH) (D : OrbitCertificate H q.1)
    (hp : profile H hH q.1 = D) :
    routeSlot H hH q =
      (BinaryS16JointAxisRouting.routeCertificate H hH q D hp).axisSlot.slot := by
  unfold routeSlot BinaryS16JointAxisRouting.axisRouting
  cases hp
  rfl

/-- Transport the complete displayed point sigma across equality of bundled
slots. -/
def routedDisplayedPointsCast {S T : Slot} (h : S = T) :
    RoutedDisplayedPoints S ≃ RoutedDisplayedPoints T :=
  Equiv.cast (congrArg RoutedDisplayedPoints h)

/-- The cell obtained by transporting one displayed point across an equality
of bundled slots. -/
def routedCellCast {S T : Slot} (h : S = T) (c : S.Cells) : T.Cells :=
  Equiv.cast (congrArg Slot.Cells h) c

/-- Transporting a slot also transports the color of each cell. -/
theorem routedColor_eq {S T : Slot} (h : S = T) (c : S.Cells) :
    S.color c = T.color (routedCellCast h c) := by
  cases h
  rfl

/-- Raw dependent transport of displayed points is the expected transport
of the cell followed by transport of its point along the color equality. -/
theorem routedDisplayedPointsCast_apply {S T : Slot} (h : S = T)
    (c : S.Cells) (y : mixturePoints (S.color c)) :
    routedDisplayedPointsCast h ⟨c,y⟩ =
      ⟨routedCellCast h c,
        Equiv.cast (congrArg mixturePoints (routedColor_eq h c)) y⟩ := by
  cases h
  rfl

/-- Stable computation rule for the private certificate dispatcher.  After
the domain is cast along `routeSlot_eq_of_profile`, the selected routed chart
followed by the selected local orbit chart is exactly the corresponding
explicit-certificate chart. -/
theorem slotChart_trans_localChart_eq_of_profile
    (q : Occurrence H hH) (D : OrbitCertificate H q.1)
    (hp : profile H hH q.1 = D) :
    (slotChart H hH q).trans
        (BinaryS16JointOrbitData.localModel H hH q.1).chart.pointEquiv =
      (routedDisplayedPointsCast
          (routeSlot_eq_of_profile H hH q D hp)).trans
        ((certificateSlotChart H hH q D hp).trans
          (BinaryS16JointOrbitData.certificateLocalModel H D).chart.pointEquiv) := by
  cases hp
  rfl

/-- Pointwise computation of the fusion-natural chart on a critical C2
route.  Keeping the equality of route colors as an argument makes this
statement stable under the opaque choice used by `profile`. -/
theorem slotChart_trans_localChart_apply_c2
    (q : Occurrence H hH)
    (e : criticalActionPoints .c2 ≃ q.1.orbit)
    (he : relabelSubgroup e (criticalActionSubgroup .c2) =
      OrbitProfileFromOrbits.orbitImage H q.1)
    (hp : profile H hH q.1 = OrbitCertificate.c2 e he)
    (c : (routeSlot H hH q).Cells)
    (hc : (routeSlot H hH q).color c = .inl .c2)
    (y : mixturePoints ((routeSlot H hH q).color c)) :
    ((slotChart H hH q).trans
        (BinaryS16JointOrbitData.localModel H hH q.1).chart.pointEquiv)
        ⟨c,y⟩ =
      e (Equiv.cast (congrArg mixturePoints hc) y) := by
  rw [slotChart_trans_localChart_eq_of_profile H hH q
    (OrbitCertificate.c2 e he) hp]
  simp only [Equiv.trans_apply]
  rw [routedDisplayedPointsCast_apply]
  unfold certificateSlotChart finOneSigma
  unfold BinaryS16JointOrbitData.certificateLocalModel
  simp only [Equiv.coe_fn_mk]
  congr 1

/-- Pointwise computation of the fusion-natural chart on a critical V4
route. -/
theorem slotChart_trans_localChart_apply_v4
    (q : Occurrence H hH)
    (e : criticalActionPoints .v4 ≃ q.1.orbit)
    (he : relabelSubgroup e (criticalActionSubgroup .v4) =
      OrbitProfileFromOrbits.orbitImage H q.1)
    (hp : profile H hH q.1 = OrbitCertificate.v4 e he)
    (c : (routeSlot H hH q).Cells)
    (hc : (routeSlot H hH q).color c = .inl .v4)
    (y : mixturePoints ((routeSlot H hH q).color c)) :
    ((slotChart H hH q).trans
        (BinaryS16JointOrbitData.localModel H hH q.1).chart.pointEquiv)
        ⟨c,y⟩ =
      e (Equiv.cast (congrArg mixturePoints hc) y) := by
  rw [slotChart_trans_localChart_eq_of_profile H hH q
    (OrbitCertificate.v4 e he) hp]
  simp only [Equiv.trans_apply]
  rw [routedDisplayedPointsCast_apply]
  unfold certificateSlotChart finOneSigma
  unfold BinaryS16JointOrbitData.certificateLocalModel
  simp only [Equiv.coe_fn_mk]
  congr 1

/-- Pointwise computation of the fusion-natural chart on a critical D8
route. -/
theorem slotChart_trans_localChart_apply_d8
    (q : Occurrence H hH)
    (e : criticalActionPoints .d8 ≃ q.1.orbit)
    (he : relabelSubgroup e (criticalActionSubgroup .d8) =
      OrbitProfileFromOrbits.orbitImage H q.1)
    (hp : profile H hH q.1 = OrbitCertificate.d8 e he)
    (c : (routeSlot H hH q).Cells)
    (hc : (routeSlot H hH q).color c = .inl .d8)
    (y : mixturePoints ((routeSlot H hH q).color c)) :
    ((slotChart H hH q).trans
        (BinaryS16JointOrbitData.localModel H hH q.1).chart.pointEquiv)
        ⟨c,y⟩ =
      e (Equiv.cast (congrArg mixturePoints hc) y) := by
  rw [slotChart_trans_localChart_eq_of_profile H hH q
    (OrbitCertificate.d8 e he) hp]
  simp only [Equiv.trans_apply]
  rw [routedDisplayedPointsCast_apply]
  unfold certificateSlotChart finOneSigma
  unfold BinaryS16JointOrbitData.certificateLocalModel
  simp only [Equiv.coe_fn_mk]
  congr 1

/-- Pointwise computation of the fusion-natural chart on a critical E8
route. -/
theorem slotChart_trans_localChart_apply_e8
    (q : Occurrence H hH)
    (e : criticalActionPoints .e8 ≃ q.1.orbit)
    (he : relabelSubgroup e (criticalActionSubgroup .e8) =
      OrbitProfileFromOrbits.orbitImage H q.1)
    (hp : profile H hH q.1 = OrbitCertificate.e8 e he)
    (c : (routeSlot H hH q).Cells)
    (hc : (routeSlot H hH q).color c = .inl .e8)
    (y : mixturePoints ((routeSlot H hH q).color c)) :
    ((slotChart H hH q).trans
        (BinaryS16JointOrbitData.localModel H hH q.1).chart.pointEquiv)
        ⟨c,y⟩ =
      e (Equiv.cast (congrArg mixturePoints hc) y) := by
  rw [slotChart_trans_localChart_eq_of_profile H hH q
    (OrbitCertificate.e8 e he) hp]
  simp only [Equiv.trans_apply]
  rw [routedDisplayedPointsCast_apply]
  unfold certificateSlotChart finOneSigma
  unfold BinaryS16JointOrbitData.certificateLocalModel
  simp only [Equiv.coe_fn_mk]
  congr 1

/-- Pointwise computation of the fusion-natural chart on the one-cell
positive cyclic-four route. -/
theorem slotChart_trans_localChart_apply_cyclicFour
    (q : Occurrence H hH)
    (W : BinaryS16CanonicalCarrierProfile.SmallOrbitWitness 4 H)
    (hpoint : Quotient.mk'' W.point = q.1)
    (R : BinaryCarrierS16TaggedPositiveRoutes.DegreeFourRoute W)
    (hp : profile H hH q.1 = OrbitCertificate.cyclicFour W hpoint R)
    (c : (routeSlot H hH q).Cells)
    (hc : (routeSlot H hH q).color c = .inr none)
    (y : mixturePoints ((routeSlot H hH q).color c)) :
    ((slotChart H hH q).trans
        (BinaryS16JointOrbitData.localModel H hH q.1).chart.pointEquiv)
        ⟨c,y⟩ =
      (BinaryS16JointOrbitData.certificateLocalModel H
          (OrbitCertificate.cyclicFour W hpoint R)).chart.pointEquiv
        (R.e (Equiv.cast (congrArg mixturePoints hc) y)) := by
  rw [slotChart_trans_localChart_eq_of_profile H hH q
    (OrbitCertificate.cyclicFour W hpoint R) hp]
  simp only [Equiv.trans_apply]
  rw [routedDisplayedPointsCast_apply]
  cases R with
  | mk e action_eq =>
      simp only [certificateSlotChart,
        BinaryCarrierS16TaggedPositiveRoutes.DegreeFourRoute.displayedPointEquiv,
        BinaryS16JointOrbitData.certificateLocalModel]
      apply congrArg
        (BinaryS16JointOrbitData.certificateLocalModel H
          (OrbitCertificate.cyclicFour W hpoint
            { e := e, action_eq := action_eq })).chart.pointEquiv
      change e ((Equiv.uniqueSigma
        (fun _ : Fin 1 => mixturePoints (.inr none))) ⟨_,_⟩) = e _
      apply congrArg e
      have hcertslot :
          (BinaryS16JointAxisRouting.routeCertificate H hH q
              (OrbitCertificate.cyclicFour W hpoint
                { e := e, action_eq := action_eq }) hp).axisSlot.slot =
            ({ e := e, action_eq := action_eq } :
              BinaryCarrierS16TaggedPositiveRoutes.DegreeFourRoute W).certified.axisSlot.slot := by
        unfold BinaryS16JointAxisRouting.routeCertificate
        simp only
        exact BinaryS16JointAxisRouting.positiveRouteC4_axisSlot_slot
          H hH q.1 q.2 W hpoint
            { e := e, action_eq := action_eq } hp
      letI : Unique
          (BinaryS16JointAxisRouting.routeCertificate H hH q
              (OrbitCertificate.cyclicFour W hpoint
                { e := e, action_eq := action_eq }) hp).axisSlot.slot.Cells := by
        rw [hcertslot]
        unfold BinaryCarrierS16TaggedPositiveRoutes.DegreeFourRoute.certified
        unfold BinaryCarrierCertifiedRetention.CertifiedPositiveAxisSlot.ofCertificate
        unfold BinaryS16CanonicalCarrierProfile.SmallOrbitWitness.quotientIdentityAxisSlot
        unfold BinaryCarrierMenuSlots.quotientIdentitySlot
        unfold BinaryCarrierMenuSlots.identitySlot
        unfold BinaryCarrierCertifiedRetention.CertifiedSlot.ofCertificate
        dsimp
        infer_instance
      rw [uniqueSigma_const_apply]
      rfl

/-- Stable equivalence-level computation on a positive degree-eight route.
The routed displayed chart is exactly the chart retained by the same
Type-valued route certificate, followed by its literal source-orbit chart. -/
theorem slotChart_trans_localChart_eq_carrier8
    (q : Occurrence H hH)
    (W : BinaryDegreeEightNormalizerSaturatedDirect.OrbitWitness H)
    (hpoint : Quotient.mk'' W.point = q.1)
    (R : BinaryCarrierS16TaggedPositiveRoutes.DegreeEightRoute W.action W.axis)
    (hp : profile H hH q.1 = OrbitCertificate.carrier8 W hpoint R) :
    (slotChart H hH q).trans
        (BinaryS16JointOrbitData.localModel H hH q.1).chart.pointEquiv =
      (routedDisplayedPointsCast
          (routeSlot_eq_of_profile H hH q
            (OrbitCertificate.carrier8 W hpoint R) hp)).trans
        (R.displayedPointEquiv.trans
          (BinaryS16JointOrbitData.certificateLocalModel H
            (OrbitCertificate.carrier8 W hpoint R)).chart.pointEquiv) := by
  simpa only [certificateSlotChart] using
    slotChart_trans_localChart_eq_of_profile H hH q
      (OrbitCertificate.carrier8 W hpoint R) hp

/-- Degree-sixteen analogue of the preceding exact chart computation.  It
includes the four-cell proper `16T1086` carrier without splitting it. -/
theorem slotChart_trans_localChart_eq_carrier16
    (q : Occurrence H hH)
    (W : BinaryDegree16PhysicalAnalyticClosure.OrbitWitness H)
    (hpoint : Quotient.mk'' W.point = q.1)
    (R : BinaryCarrierS16TaggedPositiveRoutes.DegreeSixteenRoute W.action W.axis)
    (hp : profile H hH q.1 = OrbitCertificate.carrier16 W hpoint R) :
    (slotChart H hH q).trans
        (BinaryS16JointOrbitData.localModel H hH q.1).chart.pointEquiv =
      (routedDisplayedPointsCast
          (routeSlot_eq_of_profile H hH q
            (OrbitCertificate.carrier16 W hpoint R) hp)).trans
        (R.displayedPointEquiv.trans
          (BinaryS16JointOrbitData.certificateLocalModel H
            (OrbitCertificate.carrier16 W hpoint R)).chart.pointEquiv) := by
  simpa only [certificateSlotChart] using
    slotChart_trans_localChart_eq_of_profile H hH q
      (OrbitCertificate.carrier16 W hpoint R) hp

/-- The local source actions, grouped by literal occurrence, assemble by the
canonical simultaneous orbit chart onto the original ambient labels. -/
def assemble :
    (Σ q : Occurrence H hH,
      BinaryS16JointOrbitData.Points H hH q.1) ≃ Fin (2 * N) :=
  (profilePointEquivOccurrencePoint
      (BinaryS16JointOrbitData.Points H hH)
      (BinaryS16JointOrbitData.data H hH).multiplicity).symm.trans
    (BinaryS16JointOrbitData.data H hH).chart

/-- The completed mixture selected by the exact joint word, on the original
labels of the subgroup rather than on a canonical `Fin` chart. -/
def pointChart :
    OrbitProfilePoints mixturePoints
      (profileMultiplicity
        (criticalRank
          (BinaryCarrierWordClosure.cells (routeSlot H hH))
          (BinaryCarrierWordClosure.colors (routeSlot H hH)))
        (cyclicMultiplicity
          (BinaryCarrierWordClosure.cells (routeSlot H hH))
          (BinaryCarrierWordClosure.colors (routeSlot H hH)))
        (carrierScale
          (BinaryCarrierWordClosure.cells (routeSlot H hH))
          (BinaryCarrierWordClosure.colors (routeSlot H hH)))
        (BinaryCarrierCellProfile.index
          (BinaryCarrierWordClosure.cells (routeSlot H hH))
          (BinaryCarrierWordClosure.colors (routeSlot H hH)))) ≃ Fin (2 * N) :=
  BinaryCarrierFusionNaturalPointChart.pointChart
    (routeSlot H hH)
    (fun q : Occurrence H hH => BinaryS16JointOrbitData.Points H hH q.1)
    (slotChart H hH)
    (assemble H hH)

end SymmetricSubgroupAsymptotics.BinaryS16FusionNaturalPointChart

end
