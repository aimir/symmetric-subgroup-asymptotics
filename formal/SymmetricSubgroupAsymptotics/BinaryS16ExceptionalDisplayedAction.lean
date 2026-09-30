import SymmetricSubgroupAsymptotics.BinaryS16RouteActionNaturality

/-!
# Faithful displayed actions of the fixed exceptional S16 slots

Each of the four proper carrier slots retains its original source as a
literal permutation subgroup on eight or sixteen points.  This file moves
that faithful action to the displayed carrier cells.  The construction is
invariant under equality of bundled slots, which is the form needed by the
final cross-key source reflection.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16ExceptionalDisplayedAction

open SymmetricSubgroupAsymptotics
open BinaryCarrierMenuSlots
open BinaryCarrierProfileTransport
open BinaryCarrierSlotCastNaturality
open BinaryCarrierWordClosure
open BinaryS16RouteActionNaturality
open BinaryS16RouteSlotSkeleton

/-- Native point set of a fixed exceptional source action. -/
def ExceptionalPoints : Exceptional → Type
  | .t16 => Fin 8
  | .t20 => Fin 8
  | .t21 => Fin 8
  | .t1086 => Fin 16

/-- The displayed carrier cells assembled onto the native points of their
fixed exceptional source action. -/
def exceptionalPointEquiv (e : Exceptional) :
    (Σ c : (exceptionalSlot e).Cells,
      mixturePoints ((exceptionalSlot e).color c)) ≃ ExceptionalPoints e := by
  cases e with
  | t16 => exact Equiv.uniqueSigma (fun _ : Fin 1 => Fin 8)
  | t20 => exact Equiv.uniqueSigma (fun _ : Fin 1 => Fin 8)
  | t21 => exact Equiv.uniqueSigma (fun _ : Fin 1 => Fin 8)
  | t1086 =>
      exact
        (BinaryCarrierFusionNaturalPointChart.profilePointEquivOccurrencePoint
          BinaryExceptional16PhysicalProfile.ExactProfile.pointFamily
          BinaryExceptional16PhysicalProfile.ExactProfile.multiplicity).symm.trans
            BinaryExceptional16PhysicalProfile.ExactProfile.chart

/-- The fixed source subgroup acting on its native point set. -/
def exceptionalSourcePerm (e : Exceptional) :
    (exceptionalSlot e).Source →* Equiv.Perm (ExceptionalPoints e) := by
  cases e <;> exact Subgroup.subtype _

theorem exceptionalSourcePerm_injective (e : Exceptional) :
    Function.Injective (exceptionalSourcePerm e) := by
  cases e <;> intro a b h <;> exact Subtype.ext h

/-- Faithful action of a fixed exceptional source on the points displayed by
its proper carrier. -/
def exceptionalDisplayedAction (e : Exceptional) :
    (exceptionalSlot e).Source →*
      Equiv.Perm (Σ c : (exceptionalSlot e).Cells,
        mixturePoints ((exceptionalSlot e).color c)) :=
  (exceptionalPointEquiv e).symm.permCongrHom.toMonoidHom.comp
    (exceptionalSourcePerm e)

theorem exceptionalDisplayedAction_injective (e : Exceptional) :
    Function.Injective (exceptionalDisplayedAction e) :=
  (exceptionalPointEquiv e).symm.permCongrHom.injective.comp
    (exceptionalSourcePerm_injective e)

/-- Transport the faithful fixed exceptional action back across a literal
equality of bundled route slots. -/
def transportedDisplayedAction {S : Slot} (e : Exceptional)
    (h : S = exceptionalSlot e) :
    S.Source →* Equiv.Perm
      (Σ c : S.Cells, mixturePoints (S.color c)) :=
  (displayedPointEquivOfEq h).symm.permCongrHom.toMonoidHom.comp
    ((exceptionalDisplayedAction e).comp (sourceEquivOfEq h).toMonoidHom)

theorem transportedDisplayedAction_injective {S : Slot} (e : Exceptional)
    (h : S = exceptionalSlot e) :
    Function.Injective (transportedDisplayedAction e h) :=
  (displayedPointEquivOfEq h).symm.permCongrHom.injective.comp
    ((exceptionalDisplayedAction_injective e).comp (sourceEquivOfEq h).injective)

/-- Evaluation of the transported action in the fixed native point chart.
This lemma absorbs every proof-valued cast attached to the slot equality. -/
theorem exceptionalPointEquiv_transportedDisplayedAction
    {S : Slot} (e : Exceptional) (h : S = exceptionalSlot e)
    (u : S.Source)
    (z : Σ c : S.Cells, mixturePoints (S.color c)) :
    exceptionalPointEquiv e
        (displayedPointEquivOfEq h
          (transportedDisplayedAction e h u z)) =
      exceptionalSourcePerm e (sourceEquivOfEq h u)
        (exceptionalPointEquiv e (displayedPointEquivOfEq h z)) := by
  cases h
  simp [transportedDisplayedAction, exceptionalDisplayedAction,
    sourceEquivOfEq, displayedPointEquivOfEq, Equiv.permCongr_apply]

/-- Transporting both a source element and a displayed point between two
presentations of the same fixed exceptional slot commutes with its displayed
action. -/
theorem transportedDisplayedAction_natural
    {S T : Slot} (e : Exceptional)
    (hS : S = exceptionalSlot e) (hT : T = exceptionalSlot e)
    (hST : S = T) (u : S.Source)
    (z : Σ c : S.Cells, mixturePoints (S.color c)) :
    transportedDisplayedAction e hT (sourceEquivOfEq hST u)
        (displayedPointEquivOfEq hST z) =
      displayedPointEquivOfEq hST
        (transportedDisplayedAction e hS u z) := by
  subst S
  subst T
  simp [transportedDisplayedAction, sourceEquivOfEq,
    displayedPointEquivOfEq]

/-- On a proper degree-eight route, the source equivalence and the retained
displayed-point chart describe the same faithful permutation action. -/
theorem degreeEightRoute_proper_action
    {U : Subgroup (Equiv.Perm (Fin 8))}
    {M : Subgroup U} [M.Normal]
    (R : BinaryCarrierS16TaggedPositiveRoutes.DegreeEightRoute U M)
    (e : Exceptional)
    (he : degreeEightProperKind R.tag = some e)
    (hslot : R.certified.axisSlot.slot = exceptionalSlot e)
    (u : U)
    (z : Σ c : R.certified.axisSlot.slot.Cells,
      mixturePoints (R.certified.axisSlot.slot.color c)) :
    R.displayedPointEquiv
        (transportedDisplayedAction e
          hslot
          (R.certified.axisSlot.sourceEquiv u) z) =
      (u : Equiv.Perm (Fin 8)) (R.displayedPointEquiv z) := by
  cases R with
  | base b hb t kind g hg =>
      simp [BinaryCarrierS16TaggedPositiveRoutes.DegreeEightRoute.tag,
        degreeEightProperKind] at he
  | t16 i g hg source axis =>
      have he' : e = .t16 := by
        simpa [BinaryCarrierS16TaggedPositiveRoutes.DegreeEightRoute.tag,
          degreeEightProperKind] using he.symm
      subst e
      rw [show hslot = rfl from Subsingleton.elim _ _]
      let y : Fin 8 := Equiv.uniqueSigma (fun _ : Fin 1 => Fin 8) z
      change g.symm
          (((actionConjugacyEquiv g hg u : BinaryActionRegistry8.actions i) :
            Equiv.Perm (Fin 8)) y) =
        (u : Equiv.Perm (Fin 8)) (g.symm y)
      have h := actionConjugacyEquiv_apply_point g hg u (g.symm y)
      simpa using congrArg g.symm h
  | t20 i g hg source axis =>
      have he' : e = .t20 := by
        simpa [BinaryCarrierS16TaggedPositiveRoutes.DegreeEightRoute.tag,
          degreeEightProperKind] using he.symm
      subst e
      rw [show hslot = rfl from Subsingleton.elim _ _]
      let y : Fin 8 := Equiv.uniqueSigma (fun _ : Fin 1 => Fin 8) z
      change g.symm
          (((actionConjugacyEquiv g hg u : BinaryActionRegistry8.actions i) :
            Equiv.Perm (Fin 8)) y) =
        (u : Equiv.Perm (Fin 8)) (g.symm y)
      have h := actionConjugacyEquiv_apply_point g hg u (g.symm y)
      simpa using congrArg g.symm h
  | t21 i g hg source axis =>
      have he' : e = .t21 := by
        simpa [BinaryCarrierS16TaggedPositiveRoutes.DegreeEightRoute.tag,
          degreeEightProperKind] using he.symm
      subst e
      rw [show hslot = rfl from Subsingleton.elim _ _]
      let y : Fin 8 := Equiv.uniqueSigma (fun _ : Fin 1 => Fin 8) z
      change g.symm
          (((actionConjugacyEquiv g hg u : BinaryActionRegistry8.actions i) :
            Equiv.Perm (Fin 8)) y) =
        (u : Equiv.Perm (Fin 8)) (g.symm y)
      have h := actionConjugacyEquiv_apply_point g hg u (g.symm y)
      simpa using congrArg g.symm h

/-- Degree-sixteen analogue, including the four-cell nonabelian 16T1086
carrier. -/
theorem degreeSixteenRoute_proper_action
    {U : Subgroup (Equiv.Perm (Fin 16))}
    {M : Subgroup U} [M.Normal]
    (R : BinaryCarrierS16TaggedPositiveRoutes.DegreeSixteenRoute U M)
    (e : Exceptional)
    (he : degreeSixteenProperKind R.tag = some e)
    (hslot : R.certified.axisSlot.slot = exceptionalSlot e)
    (u : U)
    (z : Σ c : R.certified.axisSlot.slot.Cells,
      mixturePoints (R.certified.axisSlot.slot.color c)) :
    R.displayedPointEquiv
        (transportedDisplayedAction e
          hslot
          (R.certified.axisSlot.sourceEquiv u) z) =
      (u : Equiv.Perm (Fin 16)) (R.displayedPointEquiv z) := by
  cases R with
  | t1086 g hg owner physical =>
      have he' : e = .t1086 := by
        simpa [BinaryCarrierS16TaggedPositiveRoutes.DegreeSixteenRoute.tag,
          degreeSixteenProperKind] using he.symm
      subst e
      rw [show hslot = rfl from Subsingleton.elim _ _]
      let y : Fin 16 :=
        ((BinaryCarrierFusionNaturalPointChart.profilePointEquivOccurrencePoint
          BinaryExceptional16PhysicalProfile.ExactProfile.pointFamily
          BinaryExceptional16PhysicalProfile.ExactProfile.multiplicity).symm.trans
            BinaryExceptional16PhysicalProfile.ExactProfile.chart) z
      change g.symm
          (exceptionalPointEquiv .t1086
            (transportedDisplayedAction .t1086 rfl
              ((BinaryCarrierS16TaggedPositiveRoutes.DegreeSixteenRoute.t1086
                g hg owner physical).certified.axisSlot.sourceEquiv u) z)) =
        (u : Equiv.Perm (Fin 16)) (g.symm y)
      have ha := exceptionalPointEquiv_transportedDisplayedAction
        .t1086 rfl
          ((BinaryCarrierS16TaggedPositiveRoutes.DegreeSixteenRoute.t1086
            g hg owner physical).certified.axisSlot.sourceEquiv u) z
      calc
        _ = g.symm
            (exceptionalSourcePerm .t1086
              (sourceEquivOfEq rfl
                ((BinaryCarrierS16TaggedPositiveRoutes.DegreeSixteenRoute.t1086
                  g hg owner physical).certified.axisSlot.sourceEquiv u))
              (exceptionalPointEquiv .t1086
                (displayedPointEquivOfEq rfl z))) := congrArg g.symm ha
        _ = (u : Equiv.Perm (Fin 16)) (g.symm y) := by
          change g.symm
              (((actionConjugacyEquiv g hg u :
                BinaryPairBinding16T1086.Original) :
                  Equiv.Perm (Fin 16)) y) =
            (u : Equiv.Perm (Fin 16)) (g.symm y)
          have h := actionConjugacyEquiv_apply_point g hg u (g.symm y)
          simpa using congrArg g.symm h
  | t1332 g hg row physical =>
      simp [BinaryCarrierS16TaggedPositiveRoutes.DegreeSixteenRoute.tag,
        degreeSixteenProperKind] at he

/-- Certificate-level proper-route naturality.  The route source equivalence,
the fixed exceptional displayed action, and the certificate point chart form
one commuting faithful action square. -/
theorem routeCertificate_proper_action
    {N : ℕ} (H : Subgroup (Equiv.Perm (Fin (2 * N))))
    (hH : BinaryS16CanonicalCarrierProfile.ResidualSector H)
    (q : Σ o, Fin ((BinaryS16JointOrbitData.data H hH).multiplicity o))
    (cert : BinaryS16DirectCertifiedOrbitProfile.OrbitCertificate H q.1)
    (hp : BinaryS16DirectCertifiedOrbitProfile.profile H hH q.1 = cert)
    (e : Exceptional)
    (he : certificateProperKind cert = some e)
    (hslot :
      (BinaryS16JointAxisRouting.routeCertificate
        H hH q cert hp).axisSlot.slot = exceptionalSlot e) :
    ∀ (u : BinaryS16JointOrbitData.action H hH q.1)
      (z : Σ c : (BinaryS16JointAxisRouting.routeCertificate
          H hH q cert hp).axisSlot.slot.Cells,
        mixturePoints
          ((BinaryS16JointAxisRouting.routeCertificate
            H hH q cert hp).axisSlot.slot.color c)),
      BinaryS16FusionNaturalPointChart.certificateSlotChartExact
          H hH q cert hp
          (transportedDisplayedAction e hslot
            ((BinaryS16JointAxisRouting.routeCertificate
              H hH q cert hp).axisSlot.sourceEquiv u) z) =
        ((BinaryS16JointAxisRouting.localModelActionEquivOfEq
          (congrArg
            (BinaryS16JointOrbitData.certificateLocalModel H) hp) u :
          (BinaryS16JointOrbitData.certificateLocalModel H cert).action) :
            Equiv.Perm _)
          (BinaryS16FusionNaturalPointChart.certificateSlotChartExact
            H hH q cert hp z) := by
  cases cert with
  | c2 point image =>
      simp [certificateProperKind] at he
  | v4 point image =>
      simp [certificateProperKind] at he
  | d8 point image =>
      simp [certificateProperKind] at he
  | e8 point image =>
      simp [certificateProperKind] at he
  | cyclicFour W hpoint R =>
      simp [certificateProperKind] at he
  | carrier8 W hpoint R =>
      intro u z
      simp only [BinaryS16JointAxisRouting.routeCertificate] at hslot ⊢
      rw [positiveRouteC8_sourceEquiv_direct H hH q W hpoint R hp]
      let v : W.action :=
        BinaryS16JointAxisRouting.localModelActionEquivOfEq
          (congrArg (BinaryS16JointOrbitData.certificateLocalModel H) hp) u
      change R.displayedPointEquiv
          (transportedDisplayedAction e hslot
            (R.certified.axisSlot.sourceEquiv v) z) =
        ((v : Equiv.Perm (Fin 8)) (R.displayedPointEquiv z))
      exact degreeEightRoute_proper_action R e he hslot v z
  | carrier16 W hpoint R =>
      intro u z
      simp only [BinaryS16JointAxisRouting.routeCertificate] at hslot ⊢
      rw [positiveRouteC16_sourceEquiv_direct H hH q W hpoint R hp]
      let v : W.action :=
        BinaryS16JointAxisRouting.localModelActionEquivOfEq
          (congrArg (BinaryS16JointOrbitData.certificateLocalModel H) hp) u
      change R.displayedPointEquiv
          (transportedDisplayedAction e hslot
            (R.certified.axisSlot.sourceEquiv v) z) =
        ((v : Equiv.Perm (Fin 16)) (R.displayedPointEquiv z))
      exact degreeSixteenRoute_proper_action R e he hslot v z

/-- Proper-route naturality for the selected canonical occurrence. -/
theorem axisRouting_proper_action
    {N : ℕ} (H : Subgroup (Equiv.Perm (Fin (2 * N))))
    (hH : BinaryS16CanonicalCarrierProfile.ResidualSector H)
    (q : Σ o, Fin ((BinaryS16JointOrbitData.data H hH).multiplicity o))
    (e : Exceptional)
    (he : properKindAt H hH q.1 = some e)
    (hslot : (BinaryS16JointAxisRouting.axisRouting
      H hH q).axisSlot.slot = exceptionalSlot e) :
    ∀ (u : BinaryS16JointOrbitData.action H hH q.1)
      (z : Σ c : (BinaryS16JointAxisRouting.axisRouting
          H hH q).axisSlot.slot.Cells,
        mixturePoints
          ((BinaryS16JointAxisRouting.axisRouting
            H hH q).axisSlot.slot.color c)),
      BinaryS16FusionNaturalPointChart.slotChart H hH q
          (transportedDisplayedAction e hslot
            ((BinaryS16JointAxisRouting.axisRouting
              H hH q).axisSlot.sourceEquiv u) z) =
        (u : Equiv.Perm _) (BinaryS16FusionNaturalPointChart.slotChart H hH q z) := by
  have he' : certificateProperKind
      (BinaryS16DirectCertifiedOrbitProfile.profile H hH q.1) = some e := by
    simpa only [properKindAt_eq_certificateProperKind] using he
  simpa only [BinaryS16JointAxisRouting.axisRouting,
    BinaryS16FusionNaturalPointChart.certificateSlotChartExact_selected,
    BinaryS16JointOrbitData.localModel,
    BinaryS16JointOrbitData.action] using
      routeCertificate_proper_action H hH q
        (BinaryS16DirectCertifiedOrbitProfile.profile H hH q.1)
        rfl e he' hslot

end SymmetricSubgroupAsymptotics.BinaryS16ExceptionalDisplayedAction

end
