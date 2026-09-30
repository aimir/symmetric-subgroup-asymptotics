import SymmetricSubgroupAsymptotics.BinaryCarrierSlotCastNaturality
import SymmetricSubgroupAsymptotics.BinaryS16FusionNaturalPointChart
import SymmetricSubgroupAsymptotics.BinaryS16RouteSlotSkeleton

/-!
# Action naturality of the S16 routed point charts

The source equivalence stored in a routed axis slot and the displayed-point
chart stored by the same Type-valued certificate describe the same action.
This is the semantic link needed by cross-key carrier reflection.  The first
part treats every quotient-identity route uniformly after its literal
identity presentation has been exposed.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.BinaryS16RouteActionNaturality

open SymmetricSubgroupAsymptotics
open BinaryCarrierMenuSlots
open BinaryCarrierProfileTransport
open BinaryCarrierSlotCastNaturality
open BinaryCarrierWordClosure
open BinaryS16DirectCertifiedOrbitProfile
open BinaryS16FusionNaturalPointChart
open BinaryS16JointOrbitData
open BinaryS16RouteSlotSkeleton

abbrev DisplayedPoints (S : Slot) :=
  Σ c : S.Cells, mixturePoints (S.color c)

/-- The action equivalence induced by an exact point relabelling. -/
def relabelActionEquiv {A B : Type} (e : A ≃ B)
    (U : Subgroup (Equiv.Perm A)) (V : Subgroup (Equiv.Perm B))
    (h : relabelSubgroup e U = V) : U ≃* V :=
  (U.equivMapOfInjective e.permCongrHom.toMonoidHom
    e.permCongrHom.injective).trans (MulEquiv.subgroupCongr h)

/-- The inverse relabelling action moves points through the inverse chart. -/
theorem relabelActionEquiv_symm_apply_point
    {A B : Type} (e : A ≃ B)
    (U : Subgroup (Equiv.Perm A)) (V : Subgroup (Equiv.Perm B))
    (h : relabelSubgroup e U = V) (u : V) (z : B) :
    e ((((relabelActionEquiv e U V h).symm u : U) : Equiv.Perm A)
        (e.symm z)) =
      (u : Equiv.Perm B) z := by
  let E := relabelActionEquiv e U V h
  have hu : e.permCongr ((E.symm u : U) : Equiv.Perm A) =
      (u : Equiv.Perm B) := by
    exact congrArg Subtype.val (E.apply_symm_apply u)
  calc
    e (((E.symm u : U) : Equiv.Perm A) (e.symm z)) =
        e.permCongr ((E.symm u : U) : Equiv.Perm A) z := by
          rw [Equiv.permCongr_apply]
    _ = (u : Equiv.Perm B) z := congrArg (fun p => p z) hu

theorem localActionEquiv_symm_apply_point
    {n w : ℕ} (G : Subgroup (Equiv.Perm (Fin n))) (x : Fin n)
    (hw : Nat.card (MulAction.orbit G x) = w)
    (e : Fin w ≃ FusionActualOrbitCharts.orbitSet G x)
    (U : Subgroup (Equiv.Perm (Fin w)))
    (himage : relabelSubgroup e U =
      OrbitProfileFromOrbits.orbitImage G
        (Quotient.mk'' x : OrbitProfileFromOrbits.Orbit G))
    (u : U) (z : Fin w) :
    let c := FusionOrbitRepresentativeAxis.chartConjugator G x hw e
    c ((((FusionOrbitRepresentativeAxis.localActionEquiv
          G x hw e U himage).symm u :
        FusionOrbitRepresentativeAxis.ActualAction G x hw) : Equiv.Perm _)
          (c.symm z)) =
      (u : Equiv.Perm _) z := by
  simp [FusionOrbitRepresentativeAxis.localActionEquiv,
    FusionOrbitRepresentativeAxis.representativeActionEquiv,
    actionConjugacyEquiv,Equiv.permCongr_apply]

theorem actionConjugacyEquiv_apply_point
    {X : Type} (g : Equiv.Perm X)
    {U V : Subgroup (Equiv.Perm X)}
    (h : MulAut.conj g • U = V) (u : U) (x : X) :
    (((actionConjugacyEquiv g h u : V) : Equiv.Perm X) (g x)) =
      g ((u : Equiv.Perm X) x) := by
  change (g * (u : Equiv.Perm X) * g⁻¹) (g x) = _
  simp

/-- With the canonical actual-orbit chart, quotient-orbit transport does not
change the local action coordinates. -/
theorem canonicalTransportData_action
    {n w : ℕ} (G : Subgroup (Equiv.Perm (Fin n))) (x : Fin n)
    (hw : Nat.card (MulAction.orbit G x) = w) :
    (FusionOrbitQuotientAxisTransport.transportData
      G x hw rfl (FusionActualOrbitCharts.orbitEquiv G x hw)
      (FusionOrbitRepresentativeAxis.ActualAction G x hw)
      (FusionOrbitRepresentativeAxis.orbitEquiv_chartAction_image G x hw)).E =
        MulEquiv.refl (FusionOrbitRepresentativeAxis.ActualAction G x hw) := by
  apply MulEquiv.ext
  intro u
  apply Subtype.ext
  apply Equiv.ext
  intro y
  have h := localActionEquiv_symm_apply_point G x hw
    (FusionActualOrbitCharts.orbitEquiv G x hw)
    (FusionOrbitRepresentativeAxis.ActualAction G x hw)
    (FusionOrbitRepresentativeAxis.orbitEquiv_chartAction_image G x hw) u y
  simpa [FusionOrbitQuotientAxisTransport.transportData,
    FusionOrbitRepresentativeAxis.chartConjugator] using h

theorem exactOrbitChart_transport_trans
    {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}
    {a b c : OrbitProfileFromOrbits.Orbit G}
    {P : Type} {U : Subgroup (Equiv.Perm P)}
    (hab : a = b) (hbc : b = c)
    (C : BinaryS16JointOrbitData.ExactOrbitChart G a P U) :
    BinaryS16JointOrbitData.ExactOrbitChart.transport G hbc
        (BinaryS16JointOrbitData.ExactOrbitChart.transport G hab C) =
      BinaryS16JointOrbitData.ExactOrbitChart.transport G (hab.trans hbc) C := by
  subst b
  subst c
  rfl

theorem transportedCanonicalTransportData_action
    {n w : ℕ} (G : Subgroup (Equiv.Perm (Fin n))) (x : Fin n)
    (hw : Nat.card (MulAction.orbit G x) = w)
    (o : OrbitProfileFromOrbits.Orbit G)
    (hpoint : (Quotient.mk'' x : OrbitProfileFromOrbits.Orbit G) = o) :
    let C : BinaryS16JointOrbitData.ExactOrbitChart G
        (Quotient.mk'' x : OrbitProfileFromOrbits.Orbit G) (Fin w)
        (FusionOrbitRepresentativeAxis.ActualAction G x hw) :=
      ⟨FusionActualOrbitCharts.orbitEquiv G x hw,
        FusionOrbitRepresentativeAxis.orbitEquiv_chartAction_image G x hw⟩
    let D := BinaryS16JointOrbitData.ExactOrbitChart.transport G hpoint C
    (FusionOrbitQuotientAxisTransport.transportData
      G x hw hpoint D.pointEquiv
      (FusionOrbitRepresentativeAxis.ActualAction G x hw) D.image_eq).E =
        MulEquiv.refl (FusionOrbitRepresentativeAxis.ActualAction G x hw) := by
  subst o
  exact canonicalTransportData_action G x hw

/-- Collapse the unique cell coordinate of a quotient-identity slot. -/
def identityDisplayedPointEquiv (g : MixtureKind) :
    DisplayedPoints (quotientIdentitySlot g (⊤ : Subgroup (mixtureAction g))) ≃
      mixturePoints g := by
  change (Σ _ : Fin 1, mixturePoints g) ≃ mixturePoints g
  exact
    { toFun := fun z => z.2
      invFun := fun x => ⟨0,x⟩
      left_inv := by
        rintro ⟨i,x⟩
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rfl
      right_inv := fun _ => rfl }

/-- The source action on an explicit one-cell family. -/
def oneCellAction (g : MixtureKind) :
    mixtureAction g →* Equiv.Perm (Σ _ : Fin 1, mixturePoints g) :=
    { toFun := fun u =>
        { toFun := fun z => ⟨z.1,(u : Equiv.Perm _) z.2⟩
          invFun := fun z => ⟨z.1,(u : Equiv.Perm _).symm z.2⟩
          left_inv := by intro z; cases z; simp
          right_inv := by intro z; cases z; simp }
      map_one' := by
        apply Equiv.ext
        rintro ⟨i,x⟩
        rfl
      map_mul' := by
        intro u v
        apply Equiv.ext
        rintro ⟨i,x⟩
        rfl }

@[simp] theorem oneCellAction_apply
    (g : MixtureKind) (u : mixtureAction g)
    (z : Σ _ : Fin 1, mixturePoints g) :
    oneCellAction g u z = ⟨z.1,(u : Equiv.Perm _) z.2⟩ := rfl

@[simp] theorem oneCellAction_natural
    (g : MixtureKind) (u : mixtureAction g) (z : mixturePoints g) :
    oneCellPointEquiv (mixturePoints g)
        (oneCellAction g u
          ((oneCellPointEquiv (mixturePoints g)).symm z)) =
      (u : Equiv.Perm _) z := by
  rfl

/-- The source action on the one displayed cell of an identity slot.  Its
definition is independent of the normal subgroup and quotient. -/
def identityDisplayedAction (g : MixtureKind) :
    mixtureAction g →* Equiv.Perm
      (DisplayedPoints (quotientIdentitySlot g
        (⊤ : Subgroup (mixtureAction g)))) := by
  change mixtureAction g →* Equiv.Perm (Σ _ : Fin 1, mixturePoints g)
  exact oneCellAction g

/-- Transport the standard one-cell action back through an exposed identity
presentation of an arbitrary bundled slot. -/
def identitySlotAction {S : Slot} (P : IdentityPresentation S) :
    S.Source →* Equiv.Perm (DisplayedPoints S) := by
  rcases P with ⟨g,N,hN,hS⟩
  subst S
  change mixtureAction g →* Equiv.Perm (Σ _ : Fin 1, mixturePoints g)
  exact oneCellAction g

variable {N : ℕ}
variable (H : Subgroup (Equiv.Perm (Fin (2 * N))))
variable (hH : BinaryS16CanonicalCarrierProfile.ResidualSector H)

theorem criticalRouteC2_sourceEquiv
    (q : Σ o, Fin ((data H hH).multiplicity o))
    (e : criticalActionPoints .c2 ≃ q.1.orbit)
    (himage : relabelSubgroup e (criticalActionSubgroup .c2) =
      OrbitProfileFromOrbits.orbitImage H q.1)
    (hp : profile H hH q.1 = .c2 e himage) :
    (BinaryS16JointAxisRouting.criticalRouteC2
      H hH q.1 q.2 e himage hp).axisSlot.sourceEquiv =
      BinaryS16JointAxisRouting.localModelActionEquivOfEq
        (congrArg (BinaryS16JointOrbitData.certificateLocalModel H) hp) := by
  rfl

theorem criticalRouteV4_sourceEquiv
    (q : Σ o, Fin ((data H hH).multiplicity o))
    (e : criticalActionPoints .v4 ≃ q.1.orbit)
    (himage : relabelSubgroup e (criticalActionSubgroup .v4) =
      OrbitProfileFromOrbits.orbitImage H q.1)
    (hp : profile H hH q.1 = .v4 e himage) :
    (BinaryS16JointAxisRouting.criticalRouteV4
      H hH q.1 q.2 e himage hp).axisSlot.sourceEquiv =
      BinaryS16JointAxisRouting.localModelActionEquivOfEq
        (congrArg (BinaryS16JointOrbitData.certificateLocalModel H) hp) := by
  rfl

theorem criticalRouteD8_sourceEquiv
    (q : Σ o, Fin ((data H hH).multiplicity o))
    (e : criticalActionPoints .d8 ≃ q.1.orbit)
    (himage : relabelSubgroup e (criticalActionSubgroup .d8) =
      OrbitProfileFromOrbits.orbitImage H q.1)
    (hp : profile H hH q.1 = .d8 e himage) :
    (BinaryS16JointAxisRouting.criticalRouteD8
      H hH q.1 q.2 e himage hp).axisSlot.sourceEquiv =
      BinaryS16JointAxisRouting.localModelActionEquivOfEq
        (congrArg (BinaryS16JointOrbitData.certificateLocalModel H) hp) := by
  rfl

theorem criticalRouteE8_sourceEquiv
    (q : Σ o, Fin ((data H hH).multiplicity o))
    (e : criticalActionPoints .e8 ≃ q.1.orbit)
    (himage : relabelSubgroup e (criticalActionSubgroup .e8) =
      OrbitProfileFromOrbits.orbitImage H q.1)
    (hp : profile H hH q.1 = .e8 e himage) :
    (BinaryS16JointAxisRouting.criticalRouteE8
      H hH q.1 q.2 e himage hp).axisSlot.sourceEquiv =
      BinaryS16JointAxisRouting.localModelActionEquivOfEq
        (congrArg (BinaryS16JointOrbitData.certificateLocalModel H) hp) := by
  rfl

theorem positiveRouteC4_sourceEquiv
    (q : Σ o, Fin ((data H hH).multiplicity o))
    (W : BinaryS16CanonicalCarrierProfile.SmallOrbitWitness 4 H)
    (hpoint : Quotient.mk'' W.point = q.1)
    (R : BinaryCarrierS16TaggedPositiveRoutes.DegreeFourRoute W)
    (hp : profile H hH q.1 = .cyclicFour W hpoint R) :
    let hmodel : BinaryS16JointOrbitData.localModel H hH q.1 =
        BinaryS16JointOrbitData.certificateLocalModel H
          (.cyclicFour W hpoint R) :=
      congrArg (BinaryS16JointOrbitData.certificateLocalModel H) hp
    let ho : q.1 = (data H hH).orbitIndex q :=
      (BinaryS16JointOrbitData.orbitIndex_eq_fst H hH q).symm
    let M := BinaryS16JointOrbitData.certificateLocalModel H
      (.cyclicFour W hpoint R)
    let D := BinaryS16JointOrbitData.ExactOrbitChart.transport H ho M.chart
    let T := FusionOrbitQuotientAxisTransport.transportData
      H W.point W.orbit_card (hpoint.trans ho)
      D.pointEquiv W.action D.image_eq
    (BinaryS16JointAxisRouting.positiveRouteC4
      H hH q.1 q.2 W hpoint R hp).axisSlot.sourceEquiv =
      ((BinaryS16JointAxisRouting.localModelActionEquivOfEq hmodel).trans
        T.E).trans R.certified.axisSlot.sourceEquiv := by
  rfl

theorem positiveRouteC4_sourceEquiv_direct
    (q : Σ o, Fin ((data H hH).multiplicity o))
    (W : BinaryS16CanonicalCarrierProfile.SmallOrbitWitness 4 H)
    (hpoint : Quotient.mk'' W.point = q.1)
    (R : BinaryCarrierS16TaggedPositiveRoutes.DegreeFourRoute W)
    (hp : profile H hH q.1 = .cyclicFour W hpoint R) :
    (BinaryS16JointAxisRouting.positiveRouteC4
      H hH q.1 q.2 W hpoint R hp).axisSlot.sourceEquiv =
      (BinaryS16JointAxisRouting.localModelActionEquivOfEq
        (congrArg (BinaryS16JointOrbitData.certificateLocalModel H) hp)).trans
          R.certified.axisSlot.sourceEquiv := by
  rw [positiveRouteC4_sourceEquiv H hH q W hpoint R hp]
  let ho : q.1 = (data H hH).orbitIndex q :=
    (BinaryS16JointOrbitData.orbitIndex_eq_fst H hH q).symm
  let C : BinaryS16JointOrbitData.ExactOrbitChart H
      (Quotient.mk'' W.point : OrbitProfileFromOrbits.Orbit H) (Fin 4)
      W.action :=
    ⟨FusionActualOrbitCharts.orbitEquiv H W.point W.orbit_card,
      BinaryS16JointOrbitData.smallWitness_image_eq H W⟩
  let D := BinaryS16JointOrbitData.ExactOrbitChart.transport H ho
    (BinaryS16JointOrbitData.certificateLocalModel H
      (.cyclicFour W hpoint R)).chart
  have hD : D = BinaryS16JointOrbitData.ExactOrbitChart.transport H
      (hpoint.trans ho) C := by
    simpa [D,C,BinaryS16JointOrbitData.certificateLocalModel] using
      exactOrbitChart_transport_trans hpoint ho C
  have hT : (FusionOrbitQuotientAxisTransport.transportData
      H W.point W.orbit_card (hpoint.trans ho)
      D.pointEquiv W.action D.image_eq).E = MulEquiv.refl W.action := by
    rw [hD]
    exact transportedCanonicalTransportData_action
      H W.point W.orbit_card ((data H hH).orbitIndex q) (hpoint.trans ho)
  rw [hT]
  rfl

theorem positiveRouteC8_sourceEquiv
    (q : Σ o, Fin ((data H hH).multiplicity o))
    (W : BinaryDegreeEightNormalizerSaturatedDirect.OrbitWitness H)
    (hpoint : Quotient.mk'' W.point = q.1)
    (R : BinaryCarrierS16TaggedPositiveRoutes.DegreeEightRoute
      W.action W.axis)
    (hp : profile H hH q.1 = .carrier8 W hpoint R) :
    let hmodel : BinaryS16JointOrbitData.localModel H hH q.1 =
        BinaryS16JointOrbitData.certificateLocalModel H
          (.carrier8 W hpoint R) :=
      congrArg (BinaryS16JointOrbitData.certificateLocalModel H) hp
    let ho : q.1 = (data H hH).orbitIndex q :=
      (BinaryS16JointOrbitData.orbitIndex_eq_fst H hH q).symm
    let M := BinaryS16JointOrbitData.certificateLocalModel H
      (.carrier8 W hpoint R)
    let D := BinaryS16JointOrbitData.ExactOrbitChart.transport H ho M.chart
    let T := FusionOrbitQuotientAxisTransport.transportData
      H W.point W.orbit_card (hpoint.trans ho)
      D.pointEquiv W.action D.image_eq
    (BinaryS16JointAxisRouting.positiveRouteC8
      H hH q.1 q.2 W hpoint R hp).axisSlot.sourceEquiv =
      ((BinaryS16JointAxisRouting.localModelActionEquivOfEq hmodel).trans
        T.E).trans R.certified.axisSlot.sourceEquiv := by
  rfl

theorem positiveRouteC8_sourceEquiv_direct
    (q : Σ o, Fin ((data H hH).multiplicity o))
    (W : BinaryDegreeEightNormalizerSaturatedDirect.OrbitWitness H)
    (hpoint : Quotient.mk'' W.point = q.1)
    (R : BinaryCarrierS16TaggedPositiveRoutes.DegreeEightRoute
      W.action W.axis)
    (hp : profile H hH q.1 = .carrier8 W hpoint R) :
    (BinaryS16JointAxisRouting.positiveRouteC8
      H hH q.1 q.2 W hpoint R hp).axisSlot.sourceEquiv =
      (BinaryS16JointAxisRouting.localModelActionEquivOfEq
        (congrArg (BinaryS16JointOrbitData.certificateLocalModel H) hp)).trans
          R.certified.axisSlot.sourceEquiv := by
  rw [positiveRouteC8_sourceEquiv H hH q W hpoint R hp]
  let ho : q.1 = (data H hH).orbitIndex q :=
    (BinaryS16JointOrbitData.orbitIndex_eq_fst H hH q).symm
  let C : BinaryS16JointOrbitData.ExactOrbitChart H
      (Quotient.mk'' W.point : OrbitProfileFromOrbits.Orbit H) (Fin 8)
      W.action :=
    ⟨FusionActualOrbitCharts.orbitEquiv H W.point W.orbit_card,
      BinaryS16JointOrbitData.witnessEight_image_eq H W⟩
  let D := BinaryS16JointOrbitData.ExactOrbitChart.transport H ho
    (BinaryS16JointOrbitData.certificateLocalModel H
      (.carrier8 W hpoint R)).chart
  have hD : D = BinaryS16JointOrbitData.ExactOrbitChart.transport H
      (hpoint.trans ho) C := by
    simpa [D,C,BinaryS16JointOrbitData.certificateLocalModel] using
      exactOrbitChart_transport_trans hpoint ho C
  have hT : (FusionOrbitQuotientAxisTransport.transportData
      H W.point W.orbit_card (hpoint.trans ho)
      D.pointEquiv W.action D.image_eq).E = MulEquiv.refl W.action := by
    rw [hD]
    exact transportedCanonicalTransportData_action
      H W.point W.orbit_card ((data H hH).orbitIndex q) (hpoint.trans ho)
  rw [hT]
  rfl

theorem positiveRouteC16_sourceEquiv
    (q : Σ o, Fin ((data H hH).multiplicity o))
    (W : BinaryDegree16PhysicalAnalyticClosure.OrbitWitness H)
    (hpoint : Quotient.mk'' W.point = q.1)
    (R : BinaryCarrierS16TaggedPositiveRoutes.DegreeSixteenRoute
      W.action W.axis)
    (hp : profile H hH q.1 = .carrier16 W hpoint R) :
    let hmodel : BinaryS16JointOrbitData.localModel H hH q.1 =
        BinaryS16JointOrbitData.certificateLocalModel H
          (.carrier16 W hpoint R) :=
      congrArg (BinaryS16JointOrbitData.certificateLocalModel H) hp
    let ho : q.1 = (data H hH).orbitIndex q :=
      (BinaryS16JointOrbitData.orbitIndex_eq_fst H hH q).symm
    let M := BinaryS16JointOrbitData.certificateLocalModel H
      (.carrier16 W hpoint R)
    let D := BinaryS16JointOrbitData.ExactOrbitChart.transport H ho M.chart
    let T := FusionOrbitQuotientAxisTransport.transportData
      H W.point W.orbit_card (hpoint.trans ho)
      D.pointEquiv W.action D.image_eq
    (BinaryS16JointAxisRouting.positiveRouteC16
      H hH q.1 q.2 W hpoint R hp).axisSlot.sourceEquiv =
      ((BinaryS16JointAxisRouting.localModelActionEquivOfEq hmodel).trans
        T.E).trans R.certified.axisSlot.sourceEquiv := by
  rfl

theorem positiveRouteC16_sourceEquiv_direct
    (q : Σ o, Fin ((data H hH).multiplicity o))
    (W : BinaryDegree16PhysicalAnalyticClosure.OrbitWitness H)
    (hpoint : Quotient.mk'' W.point = q.1)
    (R : BinaryCarrierS16TaggedPositiveRoutes.DegreeSixteenRoute
      W.action W.axis)
    (hp : profile H hH q.1 = .carrier16 W hpoint R) :
    (BinaryS16JointAxisRouting.positiveRouteC16
      H hH q.1 q.2 W hpoint R hp).axisSlot.sourceEquiv =
      (BinaryS16JointAxisRouting.localModelActionEquivOfEq
        (congrArg (BinaryS16JointOrbitData.certificateLocalModel H) hp)).trans
          R.certified.axisSlot.sourceEquiv := by
  rw [positiveRouteC16_sourceEquiv H hH q W hpoint R hp]
  let ho : q.1 = (data H hH).orbitIndex q :=
    (BinaryS16JointOrbitData.orbitIndex_eq_fst H hH q).symm
  let C : BinaryS16JointOrbitData.ExactOrbitChart H
      (Quotient.mk'' W.point : OrbitProfileFromOrbits.Orbit H) (Fin 16)
      W.action :=
    ⟨FusionActualOrbitCharts.orbitEquiv H W.point W.orbit_card,
      BinaryS16JointOrbitData.witnessSixteen_image_eq H W⟩
  let D := BinaryS16JointOrbitData.ExactOrbitChart.transport H ho
    (BinaryS16JointOrbitData.certificateLocalModel H
      (.carrier16 W hpoint R)).chart
  have hD : D = BinaryS16JointOrbitData.ExactOrbitChart.transport H
      (hpoint.trans ho) C := by
    simpa [D,C,BinaryS16JointOrbitData.certificateLocalModel] using
      exactOrbitChart_transport_trans hpoint ho C
  have hT : (FusionOrbitQuotientAxisTransport.transportData
      H W.point W.orbit_card (hpoint.trans ho)
      D.pointEquiv W.action D.image_eq).E = MulEquiv.refl W.action := by
    rw [hD]
    exact transportedCanonicalTransportData_action
      H W.point W.orbit_card ((data H hH).orbitIndex q) (hpoint.trans ho)
  rw [hT]
  rfl

theorem degreeFourRoute_action
    {W : BinaryS16CanonicalCarrierProfile.SmallOrbitWitness 4 H}
    (R : BinaryCarrierS16TaggedPositiveRoutes.DegreeFourRoute W)
    (u : W.action) (z : Fin 4) :
    R.displayedPointEquiv
        (identitySlotAction (degreeFourRoute_identityPresentation R)
          (R.certified.axisSlot.sourceEquiv u)
          (R.displayedPointEquiv.symm z)) =
      (u : Equiv.Perm _) z := by
  rcases R with ⟨e,he⟩
  change e
      ((((relabelActionEquiv e (mixtureAction (.inr none)) W.action he).symm u :
        mixtureAction (.inr none)) : Equiv.Perm _)
        (e.symm z)) = (u : Equiv.Perm _) z
  exact relabelActionEquiv_symm_apply_point
    e (mixtureAction (.inr none)) W.action he u z

theorem baseActionEquiv_symm_apply_point
    (b : BinaryDegreeEightBaseRoutes.Base)
    (u : BinaryActionRegistry8.actions
      (BinaryDegreeEightBaseRoutes.baseIndex b)) (z : Fin 8) :
    BinaryDegreeEightBaseRoutes.basePointEquiv b
        ((((BinaryDegreeEightPhysicalAnalyticClosure.baseActionEquiv b).symm u :
          mixtureAction (BinaryDegreeEightBaseRoutes.baseKind b)) :
            Equiv.Perm _) ((BinaryDegreeEightBaseRoutes.basePointEquiv b).symm z)) =
      (u : Equiv.Perm _) z := by
  exact relabelActionEquiv_symm_apply_point
    (BinaryDegreeEightBaseRoutes.basePointEquiv b)
    (mixtureAction (BinaryDegreeEightBaseRoutes.baseKind b))
    (BinaryActionRegistry8.actions (BinaryDegreeEightBaseRoutes.baseIndex b))
    (BinaryDegreeEightBaseRoutes.base_action_eq b) u z

theorem degreeEightRoute_identity_action
    {W : BinaryDegreeEightNormalizerSaturatedDirect.OrbitWitness H}
    (R : BinaryCarrierS16TaggedPositiveRoutes.DegreeEightRoute
      W.action W.axis)
    (he : degreeEightProperKind R.tag = none)
    (u : W.action) (z : Fin 8) :
    R.displayedPointEquiv
        (identitySlotAction (degreeEightRoute_identityPresentation R he)
          (R.certified.axisSlot.sourceEquiv u)
          (R.displayedPointEquiv.symm z)) =
      (u : Equiv.Perm _) z := by
  cases R with
  | base b hb t kind g hg =>
      change g.symm
          (BinaryDegreeEightBaseRoutes.basePointEquiv b
            ((((BinaryDegreeEightPhysicalAnalyticClosure.baseActionEquiv b).symm
              (actionConjugacyEquiv g hg u) :
                mixtureAction (BinaryDegreeEightBaseRoutes.baseKind b)) :
                  Equiv.Perm _)
              ((BinaryDegreeEightBaseRoutes.basePointEquiv b).symm (g z)))) =
        (u : Equiv.Perm _) z
      calc
        _ = g.symm
            (((actionConjugacyEquiv g hg u :
              BinaryActionRegistry8.actions
                (BinaryDegreeEightBaseRoutes.baseIndex b)) : Equiv.Perm _)
              (g z)) := congrArg g.symm
                (baseActionEquiv_symm_apply_point b
                  (actionConjugacyEquiv g hg u) (g z))
        _ = g.symm (g ((u : Equiv.Perm _) z)) := by
          rw [actionConjugacyEquiv_apply_point]
        _ = (u : Equiv.Perm _) z := g.symm_apply_apply _
  | t16 i g hg source axis =>
      simp [BinaryCarrierS16TaggedPositiveRoutes.DegreeEightRoute.tag,
        degreeEightProperKind] at he
  | t20 i g hg source axis =>
      simp [BinaryCarrierS16TaggedPositiveRoutes.DegreeEightRoute.tag,
        degreeEightProperKind] at he
  | t21 i g hg source axis =>
      simp [BinaryCarrierS16TaggedPositiveRoutes.DegreeEightRoute.tag,
        degreeEightProperKind] at he

theorem degreeSixteenRoute_identity_action
    {W : BinaryDegree16PhysicalAnalyticClosure.OrbitWitness H}
    (R : BinaryCarrierS16TaggedPositiveRoutes.DegreeSixteenRoute
      W.action W.axis)
    (he : degreeSixteenProperKind R.tag = none)
    (u : W.action) (z : Fin 16) :
    R.displayedPointEquiv
        (identitySlotAction (degreeSixteenRoute_identityPresentation R he)
          (R.certified.axisSlot.sourceEquiv u)
          (R.displayedPointEquiv.symm z)) =
      (u : Equiv.Perm _) z := by
  cases R with
  | t1086 g hg owner physical =>
      simp [BinaryCarrierS16TaggedPositiveRoutes.DegreeSixteenRoute.tag,
        degreeSixteenProperKind] at he
  | t1332 g hg row physical =>
      change g.symm
          (((actionConjugacyEquiv g hg u :
            BinarySelectedCatalogue16T1332.Original) : Equiv.Perm _) (g z)) =
        (u : Equiv.Perm _) z
      rw [actionConjugacyEquiv_apply_point]
      exact g.symm_apply_apply _

/-- Certificate-level identity-route naturality.  Both the source
isomorphism and the displayed-point chart come from the same certificate. -/
theorem routeCertificate_identity_action
    (q : Σ o, Fin ((data H hH).multiplicity o))
    (cert : OrbitCertificate H q.1)
    (hp : profile H hH q.1 = cert)
    (he : certificateProperKind cert = none) :
    let R := BinaryS16JointAxisRouting.routeCertificate H hH q cert hp
    let P := routeCertificate_identityPresentation H hH q cert hp he
    let E := BinaryS16JointAxisRouting.localModelActionEquivOfEq
      (congrArg (BinaryS16JointOrbitData.certificateLocalModel H) hp)
    ∀ (u : action H hH q.1)
      (z : (BinaryS16JointOrbitData.certificateLocalModel H cert).Points),
      certificateSlotChartExact H hH q cert hp
          (identitySlotAction P (R.axisSlot.sourceEquiv u)
            ((certificateSlotChartExact H hH q cert hp).symm z)) =
        ((E u :
          (BinaryS16JointOrbitData.certificateLocalModel H cert).action) :
            Equiv.Perm _ ) z := by
  cases cert with
  | c2 e himage =>
      dsimp only
      intro u z
      simp only [BinaryS16JointAxisRouting.routeCertificate]
      rw [criticalRouteC2_sourceEquiv H hH q e himage hp]
      simp [hp,identitySlotAction,
        BinaryS16JointAxisRouting.localModelActionEquivOfEq,Equiv.permCongr_apply,
        BinaryS16JointAxisRouting.criticalCertifiedSlot,
        BinaryCarrierCertifiedRetention.CertifiedSlot.ofCertificate,
        BinaryS16JointAxisRouting.routeCertificate,
        routeCertificate_identityPresentation,
        criticalRouteC2_identityPresentation,
        BinaryS16JointAxisRouting.criticalRouteC2,
        BinaryCarrierCertifiedRetention.CertifiedSlot.reindex,
        BinaryCarrierCertifiedRetention.CertifiedSlot.pullback,
        BinaryDegreeEightPhysicalAnalyticClosure.AxisSlot.pullback]
      exact oneCellAction_natural _ _ _
  | v4 e himage =>
      dsimp only
      intro u z
      simp only [BinaryS16JointAxisRouting.routeCertificate]
      rw [criticalRouteV4_sourceEquiv H hH q e himage hp]
      simp [hp,identitySlotAction,
        BinaryS16JointAxisRouting.localModelActionEquivOfEq,Equiv.permCongr_apply,
        BinaryS16JointAxisRouting.criticalCertifiedSlot,
        BinaryCarrierCertifiedRetention.CertifiedSlot.ofCertificate,
        BinaryS16JointAxisRouting.routeCertificate,
        routeCertificate_identityPresentation,
        criticalRouteV4_identityPresentation,
        BinaryS16JointAxisRouting.criticalRouteV4,
        BinaryCarrierCertifiedRetention.CertifiedSlot.reindex,
        BinaryCarrierCertifiedRetention.CertifiedSlot.pullback,
        BinaryDegreeEightPhysicalAnalyticClosure.AxisSlot.pullback]
      exact oneCellAction_natural _ _ _
  | d8 e himage =>
      dsimp only
      intro u z
      simp only [BinaryS16JointAxisRouting.routeCertificate]
      rw [criticalRouteD8_sourceEquiv H hH q e himage hp]
      simp [hp,identitySlotAction,
        BinaryS16JointAxisRouting.localModelActionEquivOfEq,Equiv.permCongr_apply,
        BinaryS16JointAxisRouting.criticalCertifiedSlot,
        BinaryCarrierCertifiedRetention.CertifiedSlot.ofCertificate,
        BinaryS16JointAxisRouting.routeCertificate,
        routeCertificate_identityPresentation,
        criticalRouteD8_identityPresentation,
        BinaryS16JointAxisRouting.criticalRouteD8,
        BinaryCarrierCertifiedRetention.CertifiedSlot.reindex,
        BinaryCarrierCertifiedRetention.CertifiedSlot.pullback,
        BinaryDegreeEightPhysicalAnalyticClosure.AxisSlot.pullback]
      exact oneCellAction_natural _ _ _
  | e8 e himage =>
      dsimp only
      intro u z
      simp only [BinaryS16JointAxisRouting.routeCertificate]
      rw [criticalRouteE8_sourceEquiv H hH q e himage hp]
      simp [hp,identitySlotAction,
        BinaryS16JointAxisRouting.localModelActionEquivOfEq,Equiv.permCongr_apply,
        BinaryS16JointAxisRouting.criticalCertifiedSlot,
        BinaryCarrierCertifiedRetention.CertifiedSlot.ofCertificate,
        BinaryS16JointAxisRouting.routeCertificate,
        routeCertificate_identityPresentation,
        criticalRouteE8_identityPresentation,
        BinaryS16JointAxisRouting.criticalRouteE8,
        BinaryCarrierCertifiedRetention.CertifiedSlot.reindex,
        BinaryCarrierCertifiedRetention.CertifiedSlot.pullback,
        BinaryDegreeEightPhysicalAnalyticClosure.AxisSlot.pullback]
      exact oneCellAction_natural _ _ _
  | cyclicFour W hpoint R =>
      dsimp only
      intro u z
      simp only [BinaryS16JointAxisRouting.routeCertificate]
      rw [positiveRouteC4_sourceEquiv_direct H hH q W hpoint R hp]
      change R.displayedPointEquiv
          (identitySlotAction (degreeFourRoute_identityPresentation R)
            (R.certified.axisSlot.sourceEquiv
              (BinaryS16JointAxisRouting.localModelActionEquivOfEq
                (congrArg
                  (BinaryS16JointOrbitData.certificateLocalModel H) hp) u))
            (R.displayedPointEquiv.symm z)) =
        ((BinaryS16JointAxisRouting.localModelActionEquivOfEq
          (congrArg (BinaryS16JointOrbitData.certificateLocalModel H) hp) u :
            W.action) : Equiv.Perm _) z
      exact degreeFourRoute_action H R _ z
  | carrier8 W hpoint R =>
      cases R with
      | base b hb t kind g hg =>
          dsimp only
          intro u z
          let R : BinaryCarrierS16TaggedPositiveRoutes.DegreeEightRoute
              W.action W.axis :=
            .base b hb t kind g hg
          have he' : degreeEightProperKind R.tag = none := by
            simpa [R, certificateProperKind] using he
          simp only [BinaryS16JointAxisRouting.routeCertificate]
          rw [positiveRouteC8_sourceEquiv_direct H hH q W hpoint R hp]
          change R.displayedPointEquiv
              (identitySlotAction (degreeEightRoute_identityPresentation R he')
                (R.certified.axisSlot.sourceEquiv
                  (BinaryS16JointAxisRouting.localModelActionEquivOfEq
                    (congrArg
                      (BinaryS16JointOrbitData.certificateLocalModel H) hp) u))
                (R.displayedPointEquiv.symm z)) =
            ((BinaryS16JointAxisRouting.localModelActionEquivOfEq
              (congrArg (BinaryS16JointOrbitData.certificateLocalModel H) hp) u :
                W.action) : Equiv.Perm _) z
          exact degreeEightRoute_identity_action H R he' _ z
      | t16 i g hg source axis =>
          change (some Exceptional.t16 : Option Exceptional) = none at he
          contradiction
      | t20 i g hg source axis =>
          change (some Exceptional.t20 : Option Exceptional) = none at he
          contradiction
      | t21 i g hg source axis =>
          change (some Exceptional.t21 : Option Exceptional) = none at he
          contradiction
  | carrier16 W hpoint R =>
      cases R with
      | t1086 g hg owner physical =>
          change (some Exceptional.t1086 : Option Exceptional) = none at he
          contradiction
      | t1332 g hg row physical =>
          dsimp only
          intro u z
          let R : BinaryCarrierS16TaggedPositiveRoutes.DegreeSixteenRoute
              W.action W.axis :=
            .t1332 g hg row physical
          have he' : degreeSixteenProperKind R.tag = none := by
            simpa [R, certificateProperKind] using he
          simp only [BinaryS16JointAxisRouting.routeCertificate]
          rw [positiveRouteC16_sourceEquiv_direct H hH q W hpoint R hp]
          change R.displayedPointEquiv
              (identitySlotAction (degreeSixteenRoute_identityPresentation R he')
                (R.certified.axisSlot.sourceEquiv
                  (BinaryS16JointAxisRouting.localModelActionEquivOfEq
                    (congrArg
                      (BinaryS16JointOrbitData.certificateLocalModel H) hp) u))
                (R.displayedPointEquiv.symm z)) =
            ((BinaryS16JointAxisRouting.localModelActionEquivOfEq
              (congrArg (BinaryS16JointOrbitData.certificateLocalModel H) hp) u :
                W.action) : Equiv.Perm _) z
          exact degreeSixteenRoute_identity_action H R he' _ z

/-- Identity-route naturality for the actual selected canonical route. -/
theorem axisRouting_identity_action
    (q : Σ o, Fin ((data H hH).multiplicity o))
    (he : properKindAt H hH q.1 = none) :
    let R := BinaryS16JointAxisRouting.axisRouting H hH q
    let P := axisRouting_identityPresentation_of_properKindAt_eq_none
      H hH q he
    ∀ (u : action H hH q.1) (z : Points H hH q.1),
      slotChart H hH q
          (identitySlotAction P (R.axisSlot.sourceEquiv u)
            ((slotChart H hH q).symm z)) = (u : Equiv.Perm _) z := by
  have he' : certificateProperKind (profile H hH q.1) = none := by
    simpa only [properKindAt_eq_certificateProperKind] using he
  simpa only [BinaryS16JointAxisRouting.axisRouting,
    axisRouting_identityPresentation_of_properKindAt_eq_none,
    certificateSlotChartExact_selected,
    BinaryS16JointOrbitData.localModel,
    BinaryS16JointOrbitData.action] using
      routeCertificate_identity_action H hH q (profile H hH q.1) rfl he'

end SymmetricSubgroupAsymptotics.BinaryS16RouteActionNaturality

end
