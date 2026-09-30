import SymmetricSubgroupAsymptotics.BinaryCarrierS16CertifiedAxisRouting
import SymmetricSubgroupAsymptotics.BinaryDegreeEightSixteenPhysicalDecoration

/-!
# Type-valued positive carrier routes with their finite tags retained

The proposition-valued carrier owners contain both the finite route branch
and the data used to construct the exact certified axis slot.  Passing only
through `Nonempty (CertifiedPositiveAxisSlot ...)` erases that correlation:
after classical choice, the selected slot cannot be proved to be the slot
described by a separately chosen route tag.

This file gives Type-valued mirrors of the positive degree-eight and
degree-sixteen owner branches.  A value determines, by projection from the
same constructor, its owner proof, finite decoration tag, and certified slot.
The critical E8 degree-eight branch is kept outside the positive package.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.BinaryCarrierS16TaggedPositiveRoutes

open SymmetricSubgroupAsymptotics
open BinaryActionRegistry8
open BinaryCarrierCertifiedRetention
open BinaryCarrierProfileTransport
open BinaryCarrierS16RouteLocalCertificates
open BinaryDegreeEightBaseRoutes
open BinaryDegreeEightCarrierSourceBridge
open BinaryDegreeEightPhysicalAnalyticClosure
open BinaryDegreeEightPhysicalDecoration
open BinaryDegreeEightSixteenPhysicalDecoration
open BinaryS16CanonicalCarrierProfile

/-! ## Degree four -/

/-- The positive width-four route before the registry chart and its exact
axis slot are separated.  Retaining `e` and `action_eq` makes the original
label chart and the slot projections of one Type-valued value. -/
structure DegreeFourRoute {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))}
    (W : SmallOrbitWitness 4 H) where
  e : mixturePoints (.inr none) ≃ Fin 4
  action_eq : relabelSubgroup e (mixtureAction (.inr none)) = W.action

namespace DegreeFourRoute

variable {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))}
  {W : SmallOrbitWitness 4 H}

/-- The exact positive slot projected from the same retained registry chart. -/
def certified (R : DegreeFourRoute W) :
    CertifiedPositiveAxisSlot W.axis 2 := by
  let S := W.quotientIdentityAxisSlot (.inr none) R.e R.action_eq
  refine CertifiedPositiveAxisSlot.ofCertificate
    (old := 2) (retained := 2) S ?_ ?_ (by omega) (by omega)
  · change ∃ c : Fin 1, ∃ t,
      (.inr none : BinaryCarrierProfileTransport.MixtureKind) = .inr t
    exact ⟨0,none,rfl⟩
  · exact cyclicFourAxisSlot_certificate W R.e R.action_eq

end DegreeFourRoute

/-- The complete four-point registry, with the positive branch retaining its
registry chart as Type-valued data.  The other two registry entries are the
literal critical V4 and D8 owners. -/
theorem widthFourRoute_nonempty_or_critical
    {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (B : SmallRegistryMixtureEquations) (hbinary : IsPGroup 2 H)
    (o : OrbitProfileFromOrbits.Orbit H)
    (hcard : Nat.card o.orbit = 4) :
    let W := BinaryS16CanonicalCarrierProfile.smallWitness
      H hbinary 4 o hcard
    Nonempty (DegreeFourRoute W) ∨
      (∃ i : CriticalActionKind,
        ∃ e : criticalActionPoints i ≃ o.orbit,
          relabelSubgroup e (criticalActionSubgroup i) =
            OrbitProfileFromOrbits.orbitImage H o) := by
  let W := BinaryS16CanonicalCarrierProfile.smallWitness H hbinary 4 o hcard
  have htrans : PermutationSubgroupTransitive W.action := by
    intro x y
    obtain ⟨u,hu⟩ := MulAction.exists_smul_eq W.action x y
    exact ⟨u,u.property,hu⟩
  obtain ⟨k,g,hg⟩ := BinaryMenuSmallCoverage.width4_complete
    W.action W.action_binary htrans
  let e := (B.point4 k).trans g.symm
  have he : relabelSubgroup e
      (mixtureAction (BinaryS16CanonicalCarrierProfile.smallKind4 k)) =
        W.action :=
    BinaryS16CanonicalCarrierProfile.small_relabel_of_registry
      H W g hg (B.point4 k) (B.image4 k)
  fin_cases k
  · exact Or.inl ⟨⟨e,he⟩⟩
  · right
    refine ⟨.v4,?_⟩
    have hc := W.criticalOrbit_of_relabel_quotient .v4 e he
    have hpoint : Quotient.mk'' W.point = o := by
      dsimp [W,BinaryS16CanonicalCarrierProfile.smallWitness]
      exact Quotient.out_eq' o
    exact BinaryS16CanonicalCarrierProfile.criticalChart_transport
      H .v4 hpoint hc
  · right
    refine ⟨.d8,?_⟩
    have hc := W.criticalOrbit_of_relabel_quotient .d8 e he
    have hpoint : Quotient.mk'' W.point = o := by
      dsimp [W,BinaryS16CanonicalCarrierProfile.smallWitness]
      exact Quotient.out_eq' o
    exact BinaryS16CanonicalCarrierProfile.criticalChart_transport
      H .d8 hpoint hc

/-! ## Degree eight -/

/-- A positive degree-eight carrier branch, before its route constructor is
erased into a proposition-valued owner.  The excluded base route is precisely
the already-owned critical E8 action. -/
inductive DegreeEightRoute
    (U : Subgroup (Equiv.Perm (Fin 8)))
    (N : Subgroup U) [N.Normal] : Type
  | base (b : Base) (hb : b ≠ .e8)
      (t : BinaryCarrierOriginalCyclicFourHall.Target)
      (kind : baseKind b = .inr t)
      (g : Equiv.Perm (Fin 8))
      (hg : MulAut.conj g • U = actions (baseIndex b))
  | t16 (i : Fin 26) (g : Equiv.Perm (Fin 8))
      (hg : MulAut.conj g • U = actions i)
      (source : (binaryEightTransportChart 0).source = actions i)
      (axis : (binaryEightTransportChart 0).axis =
        (actionConjugacyNormal g hg N).map (actions i).subtype)
  | t20 (i : Fin 26) (g : Equiv.Perm (Fin 8))
      (hg : MulAut.conj g • U = actions i)
      (source : (binaryEightTransportChart 1).source = actions i)
      (axis : (binaryEightTransportChart 1).axis =
        (actionConjugacyNormal g hg N).map (actions i).subtype)
  | t21 (i : Fin 26) (g : Equiv.Perm (Fin 8))
      (hg : MulAut.conj g • U = actions i)
      (source : (binaryEightTransportChart 2).source = actions i)
      (axis : (binaryEightTransportChart 2).axis =
        (actionConjugacyNormal g hg N).map (actions i).subtype)

namespace DegreeEightRoute

variable {U : Subgroup (Equiv.Perm (Fin 8))}
  {N : Subgroup U} [N.Normal]

/-- Forget the Type-valued route but retain its exact proposition-valued
carrier owner. -/
def owner : DegreeEightRoute U N → CarrierOwner U N
  | .base b _ _ _ g hg => .base b g hg
  | .t16 i g hg source axis => .exceptional i g hg 0 source axis
  | .t20 i g hg source axis => .exceptional i g hg 1 source axis
  | .t21 i g hg source axis => .exceptional i g hg 2 source axis

/-- The finite tag written into the mixed block table. -/
def tag : DegreeEightRoute U N → LocalRouteTag
  | .base b _ _ _ _ _ => .base b
  | .t16 _ _ _ _ _ => .exceptional 0
  | .t20 _ _ _ _ _ => .exceptional 1
  | .t21 _ _ _ _ _ => .exceptional 2

/-- Placement from the route's registry action to the actual chart action.
The finite tag determines the fixed displayed-output-to-registry chart; this
equivalence is the remaining registry-to-actual-support placement. -/
def sourcePointEquiv : DegreeEightRoute U N → Fin 8 ≃ Fin 8
  | .base _ _ _ _ g _ => g.symm
  | .t16 _ g _ _ _ => g.symm
  | .t20 _ g _ _ _ => g.symm
  | .t21 _ g _ _ _ => g.symm

/-- The tag is the route tag of the same owner constructor. -/
theorem tag_matches (R : DegreeEightRoute U N) :
    MatchesOwnerRouteTag R.owner R.tag := by
  cases R with
  | base b hb t kind g hg => exact Or.inl ⟨b,g,hg,rfl⟩
  | t16 i g hg source axis =>
      exact Or.inr ⟨i,g,hg,0,source,axis,rfl⟩
  | t20 i g hg source axis =>
      exact Or.inr ⟨i,g,hg,1,source,axis,rfl⟩
  | t21 i g hg source axis =>
      exact Or.inr ⟨i,g,hg,2,source,axis,rfl⟩

/-- The exact certified slot determined by this same route constructor. -/
def certified : DegreeEightRoute U N → CertifiedPositiveAxisSlot N 4
  | .base b hb t kind g hg => by
      let S := baseAxisSlot b g hg N
      refine CertifiedPositiveAxisSlot.ofCertificate
        (old := 4) (retained := 4)
        (S.pullback (actionConjugacyEquiv g hg) N) ?_ ?_ (by omega) (by omega)
      · change S.HasNoncritical
        change ∃ c : Fin 1, ∃ t,
          baseKind b = .inr t
        exact ⟨0,t,kind⟩
      · exact Certificate.pullback (actionConjugacyEquiv g hg) S
          (degreeEightBase_certificate b hb g hg N)
  | .t16 i g hg source axis => by
      let S := t16AxisSlot i source (actionConjugacyNormal g hg N) axis
      refine CertifiedPositiveAxisSlot.ofCertificate
        (old := 4) (retained := 4)
        (S.pullback (actionConjugacyEquiv g hg) N) ?_ ?_ (by omega) (by omega)
      · change S.HasNoncritical
        exact t16AxisSlot_hasNoncritical i source _ axis
      · exact Certificate.pullback (actionConjugacyEquiv g hg) S
          (t16AxisSlot_certificate i source _ axis)
  | .t20 i g hg source axis => by
      let S := t20AxisSlot i source (actionConjugacyNormal g hg N) axis
      refine CertifiedPositiveAxisSlot.ofCertificate
        (old := 4) (retained := 4)
        (S.pullback (actionConjugacyEquiv g hg) N) ?_ ?_ (by omega) (by omega)
      · change S.HasNoncritical
        exact t20AxisSlot_hasNoncritical i source _ axis
      · exact Certificate.pullback (actionConjugacyEquiv g hg) S
          (t20AxisSlot_certificate i source _ axis)
  | .t21 i g hg source axis => by
      let S := t21AxisSlot i source (actionConjugacyNormal g hg N) axis
      refine CertifiedPositiveAxisSlot.ofCertificate
        (old := 4) (retained := 4)
        (S.pullback (actionConjugacyEquiv g hg) N) ?_ ?_ (by omega) (by omega)
      · change S.HasNoncritical
        exact t21AxisSlot_hasNoncritical i source _ axis
      · exact Certificate.pullback (actionConjugacyEquiv g hg) S
          (t21AxisSlot_certificate i source _ axis)

/-- The same route and the canonical actual-orbit chart form the semantic
degree-eight record used by the mixed decoration. -/
def changedBlock {m : ℕ}
    {H : Subgroup (Equiv.Perm (Fin (2 * m)))}
    {o : OrbitProfileFromOrbits.Orbit H}
    (W : BinaryDegreeEightNormalizerSaturatedDirect.OrbitWitness H)
    (hpoint : Quotient.mk'' W.point = o)
    (R : DegreeEightRoute W.action W.axis) : ChangedBlock H := by
  subst o
  exact {
    orbit := ⟨Quotient.mk'' W.point,W.orbit_card⟩
    route := R.tag
    chart := R.sourcePointEquiv.trans
      (FusionActualOrbitCharts.orbitEquiv H W.point W.orbit_card) }

end DegreeEightRoute

/-- Owner-level construction of the retained positive route.  The only
non-positive alternative is the intrinsic critical E8 action. -/
theorem degreeEightRoute_nonempty_or_e8
    {U : Subgroup (Equiv.Perm (Fin 8))}
    {N : Subgroup U} [N.Normal]
    (O : CarrierOwner U N) :
    Nonempty (DegreeEightRoute U N) ∨ IsE8Action U := by
  rcases O with ⟨b,g,hg⟩ | ⟨i,g,hg,e,source,axis⟩
  · rcases base_noncritical_or_e8 b with ⟨t,kind⟩ | rfl
    · have hb : b ≠ .e8 := by
        intro h
        subst b
        simp [baseKind] at kind
      exact Or.inl ⟨DegreeEightRoute.base b hb t kind g hg⟩
    · right
      refine ⟨(basePointEquiv .e8).trans g.symm,?_⟩
      change relabelSubgroup g U = actions (baseIndex .e8) at hg
      calc
        relabelSubgroup ((basePointEquiv .e8).trans g.symm)
            (criticalActionSubgroup .e8) =
            relabelSubgroup g.symm
              (relabelSubgroup (basePointEquiv .e8)
                (criticalActionSubgroup .e8)) :=
          (relabelSubgroup_trans (basePointEquiv .e8) g.symm _).symm
        _ = relabelSubgroup g.symm (actions (baseIndex .e8)) := by
          exact congrArg (relabelSubgroup g.symm) (base_action_eq .e8)
        _ = relabelSubgroup g.symm (relabelSubgroup g U) := by rw [hg]
        _ = U := relabelSubgroup_symm g U
  · fin_cases e
    · exact Or.inl ⟨DegreeEightRoute.t16 i g hg source axis⟩
    · exact Or.inl ⟨DegreeEightRoute.t20 i g hg source axis⟩
    · exact Or.inl ⟨DegreeEightRoute.t21 i g hg source axis⟩

/-- Residual-family wrapper with the all-witness quantifier retained. -/
theorem degreeEightResidualRoute_nonempty_or_isE8Orbit
    {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))}
    (hH : H ∈ BinaryDegreeEightNormalizerSaturatedDirect.carrierResidualFamily n)
    (W : BinaryDegreeEightNormalizerSaturatedDirect.OrbitWitness H) :
    Nonempty (DegreeEightRoute W.action W.axis) ∨
      BinaryDegreeEightCarrierSourceBridge.IsE8Orbit W := by
  rcases degreeEightRoute_nonempty_or_e8
      (BinaryDegreeEightNormalizerSaturatedDirect.carrierResidual_all_witnesses
        hH W) with hroute | hE8
  · exact Or.inl hroute
  · exact Or.inr (isE8Orbit_of_isE8Action W hE8)

/-! ## Degree sixteen -/

/-- Type-valued mirror of the two positive degree-sixteen carrier owners. -/
inductive DegreeSixteenRoute
    (U : Subgroup (Equiv.Perm (Fin 16)))
    (N : Subgroup U) [N.Normal] : Type
  | t1086 (g : Equiv.Perm (Fin 16))
      (hg : MulAut.conj g • U = BinaryPairBinding16T1086.Original)
      (owner : BinaryExceptional16CyclicOwner.AxisOwner
        (actionConjugacyNormal g hg N))
      (physical : ∃ H : BinaryCarrierMixtureCompletion.Family 8,
        H.1 = BinaryNormalTransport16T1086.chart.carrier)
  | t1332 (g : Equiv.Perm (Fin 16))
      (hg : MulAut.conj g • U = BinarySelectedCatalogue16T1332.Original)
      (row : ∃ label : BinaryCarrierMasterMenu.Label,
        (BinaryCarrierWord.actualRow
          (A := BinaryCarrierMasterEnvelopeCoverage16T1332.factor)
          ⟨actionConjugacyNormal g hg N,
            actionConjugacyNormal_normal g hg N⟩).EffectivelyBoundedBy
              (BinaryCarrierMasterMenu.envelope label))
      (physical : ∃ H : BinaryCarrierMixtureCompletion.Family 8, H.1 = U)

namespace DegreeSixteenRoute

variable {U : Subgroup (Equiv.Perm (Fin 16))}
  {N : Subgroup U} [N.Normal]

def owner : DegreeSixteenRoute U N →
    BinaryDegree16SplitAnalyticClosure.CarrierOwner U N
  | .t1086 g hg owner physical => .t1086 g hg ⟨owner⟩ physical
  | .t1332 g hg row physical => .t1332 g hg row physical

def tag : DegreeSixteenRoute U N → Degree16RouteTag
  | .t1086 _ _ _ _ => .t1086
  | .t1332 _ _ _ _ => .t1332

/-- Placement from the selected catalogue action to the actual chart action.
Together with the route-tagged fixed output chart this gives the complete
displayed-output-to-actual-support placement. -/
def sourcePointEquiv : DegreeSixteenRoute U N → Fin 16 ≃ Fin 16
  | .t1086 g _ _ _ => g.symm
  | .t1332 g _ _ _ => g.symm

theorem tag_matches (R : DegreeSixteenRoute U N) :
    MatchesCarrierOwnerRouteTag R.owner R.tag := by
  cases R with
  | t1086 g hg owner physical =>
      exact ⟨g,hg,⟨owner⟩,physical,rfl⟩
  | t1332 g hg row physical =>
      exact ⟨g,hg,row,physical,rfl⟩

/-- The exact certified slot selected by the same degree-sixteen branch. -/
def certified : DegreeSixteenRoute U N → CertifiedPositiveAxisSlot N 8
  | .t1086 g hg owner _ => by
      let S := BinaryDegree16CarrierRouting.t1086AxisSlot
        (actionConjugacyNormal g hg N) owner
      refine CertifiedPositiveAxisSlot.ofCertificate
        (old := 8) (retained := 2)
        (S.pullback (actionConjugacyEquiv g hg) N) ?_ ?_ (by omega) (by omega)
      · change S.HasNoncritical
        exact BinaryDegree16CarrierRouting.t1086AxisSlot_hasNoncritical _ owner
      · exact Certificate.pullback (actionConjugacyEquiv g hg) S
          (t1086AxisSlot_certificate _ owner)
  | .t1332 g hg _ _ => by
      let S := BinaryDegree16CarrierRouting.t1332AxisSlot
        (actionConjugacyNormal g hg N)
      letI : (actionConjugacyNormal g hg N).Normal :=
        actionConjugacyNormal_normal g hg N
      letI : (N.map (actionConjugacyEquiv g hg).toMonoidHom).Normal :=
        Subgroup.Normal.map inferInstance _ (actionConjugacyEquiv g hg).surjective
      refine CertifiedPositiveAxisSlot.ofCertificate
        (old := 8) (retained := 8)
        (S.pullback (actionConjugacyEquiv g hg) N) ?_ ?_ (by omega) (by omega)
      · change S.HasNoncritical
        exact BinaryDegree16CarrierRouting.t1332AxisSlot_hasNoncritical _
      · exact Certificate.pullback (actionConjugacyEquiv g hg) S
          (t1332AxisSlot_certificate _)

/-- The route and canonical actual-orbit chart form the semantic
degree-sixteen record used by the mixed decoration. -/
def changedBlock {m : ℕ}
    {H : Subgroup (Equiv.Perm (Fin (2 * m)))}
    {o : OrbitProfileFromOrbits.Orbit H}
    (W : BinaryDegree16PhysicalAnalyticClosure.OrbitWitness H)
    (hpoint : Quotient.mk'' W.point = o)
    (R : DegreeSixteenRoute W.action W.axis) : ChangedDegree16Block H := by
  subst o
  exact {
    orbit := ⟨Quotient.mk'' W.point,W.orbit_card⟩
    route := R.tag
    chart := R.sourcePointEquiv.trans
      (FusionActualOrbitCharts.orbitEquiv H W.point W.orbit_card) }

end DegreeSixteenRoute

theorem degreeSixteenRoute_nonempty
    {U : Subgroup (Equiv.Perm (Fin 16))}
    {N : Subgroup U} [N.Normal]
    (O : BinaryDegree16SplitAnalyticClosure.CarrierOwner U N) :
    Nonempty (DegreeSixteenRoute U N) := by
  rcases O with ⟨g,hg,owner,physical⟩ | ⟨g,hg,row,physical⟩
  · obtain ⟨owner⟩ := owner
    exact ⟨DegreeSixteenRoute.t1086 g hg owner physical⟩
  · exact ⟨DegreeSixteenRoute.t1332 g hg row physical⟩

/-- Residual-family wrapper: every eligible physical sixteen-point witness
retains one complete Type-valued route. -/
theorem degreeSixteenResidualRoute_nonempty
    {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))}
    (hH : H ∈ BinaryDegree16PhysicalAnalyticClosure.carrierResidualFamily n)
    (W : BinaryDegree16PhysicalAnalyticClosure.OrbitWitness H) :
    Nonempty (DegreeSixteenRoute W.action W.axis) :=
  degreeSixteenRoute_nonempty
    (BinaryDegree16PhysicalAnalyticClosure.carrierResidual_all_witnesses hH W)

end SymmetricSubgroupAsymptotics.BinaryCarrierS16TaggedPositiveRoutes

end
