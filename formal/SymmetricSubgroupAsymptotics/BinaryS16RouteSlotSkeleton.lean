import SymmetricSubgroupAsymptotics.BinaryS16JointAxisRouting
import SymmetricSubgroupAsymptotics.BinaryS16CanonicalMixedBlockTable

/-!
# The four fixed proper-carrier skeletons in the S16 word

Most S16 routes are quotient-identity slots.  Their displayed carrier is the
one-cell full carrier and only their quotient kernel varies with the source
axis.  Exactly four route tags use a proper replacement carrier: the three
exceptional degree-eight tags and `16T1086`.  This file extracts that finite
skeleton directly from the mixed record.

The proper slots are literal values of `BinaryCarrierMenuSlots.exceptionalSlot`;
all conjugacy, canonical-axis transport, and proof-valued owner data disappear
before this projection.  This is the fixed-carrier input for the final
cross-variable reconstruction theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16RouteSlotSkeleton

open SymmetricSubgroupAsymptotics
open BinaryCarrierCanonicalOrbitPhysicalEncoding
open BinaryCarrierMenuSlots
open BinaryCarrierProfileTransport
open BinaryCarrierS16TaggedPositiveRoutes
open BinaryCarrierWordClosure
open BinaryDegreeEightBaseRoutes
open BinaryDegreeEightPhysicalAnalyticClosure
open BinaryDegreeEightPhysicalDecoration
open BinaryDegreeEightSixteenPhysicalDecoration
open BinaryS16DirectCertifiedOrbitProfile
open BinaryS16JointOrbitData

/-- The proper carrier selected by a degree-eight route tag, if any. -/
def degreeEightProperKind : LocalRouteTag → Option Exceptional
  | .base _ => none
  | .exceptional e =>
      match e.val with
      | 0 => some .t16
      | 1 => some .t20
      | _ => some .t21

/-- The proper carrier selected by a degree-sixteen route tag, if any. -/
def degreeSixteenProperKind : Degree16RouteTag → Option Exceptional
  | .t1086 => some .t1086
  | .t1332 => none

/-- Read the proper-carrier skeleton from one literal mixed record. -/
def properKind {N : ℕ} : MixedBlockRecord N → Option Exceptional
  | .degree8 r => degreeEightProperKind r.route
  | .degree16 r => degreeSixteenProperKind r.route

/-- The proper-carrier discriminator read directly from an orbit
certificate.  It agrees with `properKind` of the optional mixed record, but
is convenient for reducing the routed slot in the same certificate match. -/
def certificateProperKind
    {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))}
    {o : OrbitProfileFromOrbits.Orbit H} :
    OrbitCertificate H o → Option Exceptional
  | .carrier8 _ _ R => degreeEightProperKind R.tag
  | .carrier16 _ _ R => degreeSixteenProperKind R.tag
  | _ => none

/-- A routed slot on the unchanged side is literally a quotient-identity
slot.  The normality proof is retained in the presentation because the
quotient type depends on it. -/
structure IdentityPresentation (S : Slot) where
  kind : MixtureKind
  axis : Subgroup (mixtureAction kind)
  axisNormal : axis.Normal
  slot_eq : S = @quotientIdentitySlot kind axis axisNormal

namespace IdentityPresentation

/-- Transport an identity presentation across equality of bundled slots. -/
def cast {S T : Slot} (h : S = T) (P : IdentityPresentation S) :
    IdentityPresentation T := by
  subst T
  exact P

end IdentityPresentation

/-- A degree-eight proper tag determines the literal physical slot, with no
dependence on the registry index, conjugator, axis, or owner proof. -/
theorem degreeEightRoute_slot_eq_exceptional
    {U : Subgroup (Equiv.Perm (Fin 8))}
    {M : Subgroup U} [M.Normal]
    (R : DegreeEightRoute U M) (e : Exceptional)
    (he : degreeEightProperKind R.tag = some e) :
    R.certified.axisSlot.slot = exceptionalSlot e := by
  cases R with
  | base b hb t kind g hg =>
      simp [DegreeEightRoute.tag,degreeEightProperKind] at he
  | t16 i g hg source axis =>
      have : e = .t16 := by
        simpa [DegreeEightRoute.tag,degreeEightProperKind] using he.symm
      subst e
      rfl
  | t20 i g hg source axis =>
      have : e = .t20 := by
        simpa [DegreeEightRoute.tag,degreeEightProperKind] using he.symm
      subst e
      rfl
  | t21 i g hg source axis =>
      have : e = .t21 := by
        simpa [DegreeEightRoute.tag,degreeEightProperKind] using he.symm
      subst e
      rfl

/-- A degree-sixteen proper tag likewise leaves exactly the fixed `16T1086`
slot.  The `16T1332` constructor is an identity slot and cannot satisfy the
hypothesis. -/
theorem degreeSixteenRoute_slot_eq_exceptional
    {U : Subgroup (Equiv.Perm (Fin 16))}
    {M : Subgroup U} [M.Normal]
    (R : DegreeSixteenRoute U M) (e : Exceptional)
    (he : degreeSixteenProperKind R.tag = some e) :
    R.certified.axisSlot.slot = exceptionalSlot e := by
  cases R with
  | t1086 g hg owner physical =>
      have : e = .t1086 := by
        simpa [DegreeSixteenRoute.tag,degreeSixteenProperKind] using he.symm
      subst e
      rfl
  | t1332 g hg row physical =>
      simp [DegreeSixteenRoute.tag,degreeSixteenProperKind] at he

/-- A degree-eight route whose proper discriminator is absent is literally
one quotient-identity slot. -/
def degreeEightRoute_identityPresentation
    {U : Subgroup (Equiv.Perm (Fin 8))}
    {M : Subgroup U} [M.Normal]
    (R : DegreeEightRoute U M)
    (he : degreeEightProperKind R.tag = none) :
    IdentityPresentation R.certified.axisSlot.slot := by
  cases R with
  | base b hb t kind g hg =>
      let A := baseAlphabetAxis b g hg M
      letI : A.Normal := baseAlphabetAxis_normal b g hg M
      refine ⟨baseKind b,A,inferInstance,?_⟩
      rfl
  | t16 i g hg source axis =>
      simp [DegreeEightRoute.tag,degreeEightProperKind] at he
  | t20 i g hg source axis =>
      simp [DegreeEightRoute.tag,degreeEightProperKind] at he
  | t21 i g hg source axis =>
      simp [DegreeEightRoute.tag,degreeEightProperKind] at he

/-- The nonproper degree-sixteen route is the literal `16T1332`
quotient-identity slot. -/
def degreeSixteenRoute_identityPresentation
    {U : Subgroup (Equiv.Perm (Fin 16))}
    {M : Subgroup U} [M.Normal]
    (R : DegreeSixteenRoute U M)
    (he : degreeSixteenProperKind R.tag = none) :
    IdentityPresentation R.certified.axisSlot.slot := by
  cases R with
  | t1086 g hg owner physical =>
      simp [DegreeSixteenRoute.tag,degreeSixteenProperKind] at he
  | t1332 g hg row physical =>
      let A := actionConjugacyNormal g hg M
      letI : A.Normal := actionConjugacyNormal_normal g hg M
      let L : Subgroup (mixtureAction
          (.inr (some (.degree16 .t1332)))) :=
        A.map BinaryDegree16CarrierRouting.t1332ActionEquiv.toMonoidHom
      letI : L.Normal := Subgroup.Normal.map inferInstance _
        BinaryDegree16CarrierRouting.t1332ActionEquiv.surjective
      refine ⟨.inr (some (.degree16 .t1332)),L,inferInstance,?_⟩
      rfl

/-- Every positive cyclic-four route is a literal quotient-identity slot. -/
def degreeFourRoute_identityPresentation
    {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}
    {W : BinaryS16CanonicalCarrierProfile.SmallOrbitWitness 4 G}
    (R : DegreeFourRoute W) :
    IdentityPresentation R.certified.axisSlot.slot := by
  rcases R with ⟨e,he⟩
  let E : mixtureAction (.inr none) ≃* W.action :=
    ((mixtureAction (.inr none)).equivMapOfInjective
      e.permCongrHom.toMonoidHom e.permCongrHom.injective).trans
      (MulEquiv.subgroupCongr he)
  let A : Subgroup (mixtureAction (.inr none)) :=
    W.axis.map E.symm.toMonoidHom
  letI : A.Normal := Subgroup.Normal.map inferInstance _ E.symm.surjective
  refine ⟨.inr none,A,inferInstance,?_⟩
  rfl

/-! ## Access through the canonical S16 axis routing -/

variable {n : ℕ}
variable (H : Subgroup (Equiv.Perm (Fin n)))
variable (hH : BinaryS16CanonicalCarrierProfile.ResidualSector H)

/-- A critical C2 route is a quotient-identity slot.  The axis is written in
the certificate's fixed C2 action coordinates; canonical-axis pullback changes
only the `AxisSlot.sourceEquiv`, not this literal slot. -/
def criticalRouteC2_identityPresentation
    (o : OrbitProfileFromOrbits.Orbit H)
    (j : Fin ((data H hH).multiplicity o))
    (e : criticalActionPoints .c2 ≃ o.orbit)
    (he : relabelSubgroup e (criticalActionSubgroup .c2) =
      OrbitProfileFromOrbits.orbitImage H o)
    (hp : profile H hH o = .c2 e he) :
    IdentityPresentation
      (BinaryS16JointAxisRouting.criticalRouteC2
        H hH o j e he hp).axisSlot.slot := by
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
  let E := BinaryS16JointAxisRouting.localModelActionEquivOfEq hmodel
  let M := N.map E.toMonoidHom
  have hM : M.Normal := Subgroup.Normal.map hN E.toMonoidHom E.surjective
  refine ⟨.inl .c2,M,hM,?_⟩
  unfold BinaryS16JointAxisRouting.criticalRouteC2
  change @quotientIdentitySlot (.inl .c2) (N.map E.toMonoidHom) hM =
    @quotientIdentitySlot (.inl .c2) M hM
  rfl

/-- Critical V4 routes have the same literal identity-slot form. -/
def criticalRouteV4_identityPresentation
    (o : OrbitProfileFromOrbits.Orbit H)
    (j : Fin ((data H hH).multiplicity o))
    (e : criticalActionPoints .v4 ≃ o.orbit)
    (he : relabelSubgroup e (criticalActionSubgroup .v4) =
      OrbitProfileFromOrbits.orbitImage H o)
    (hp : profile H hH o = .v4 e he) :
    IdentityPresentation
      (BinaryS16JointAxisRouting.criticalRouteV4
        H hH o j e he hp).axisSlot.slot := by
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
  let E := BinaryS16JointAxisRouting.localModelActionEquivOfEq hmodel
  let M := N.map E.toMonoidHom
  have hM : M.Normal := Subgroup.Normal.map hN E.toMonoidHom E.surjective
  refine ⟨.inl .v4,M,hM,?_⟩
  unfold BinaryS16JointAxisRouting.criticalRouteV4
  change @quotientIdentitySlot (.inl .v4) (N.map E.toMonoidHom) hM =
    @quotientIdentitySlot (.inl .v4) M hM
  rfl

/-- Critical D8 routes have the same literal identity-slot form. -/
def criticalRouteD8_identityPresentation
    (o : OrbitProfileFromOrbits.Orbit H)
    (j : Fin ((data H hH).multiplicity o))
    (e : criticalActionPoints .d8 ≃ o.orbit)
    (he : relabelSubgroup e (criticalActionSubgroup .d8) =
      OrbitProfileFromOrbits.orbitImage H o)
    (hp : profile H hH o = .d8 e he) :
    IdentityPresentation
      (BinaryS16JointAxisRouting.criticalRouteD8
        H hH o j e he hp).axisSlot.slot := by
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
  let E := BinaryS16JointAxisRouting.localModelActionEquivOfEq hmodel
  let M := N.map E.toMonoidHom
  have hM : M.Normal := Subgroup.Normal.map hN E.toMonoidHom E.surjective
  refine ⟨.inl .d8,M,hM,?_⟩
  unfold BinaryS16JointAxisRouting.criticalRouteD8
  change @quotientIdentitySlot (.inl .d8) (N.map E.toMonoidHom) hM =
    @quotientIdentitySlot (.inl .d8) M hM
  rfl

/-- Critical E8 routes have the same literal identity-slot form. -/
def criticalRouteE8_identityPresentation
    (o : OrbitProfileFromOrbits.Orbit H)
    (j : Fin ((data H hH).multiplicity o))
    (e : criticalActionPoints .e8 ≃ o.orbit)
    (he : relabelSubgroup e (criticalActionSubgroup .e8) =
      OrbitProfileFromOrbits.orbitImage H o)
    (hp : profile H hH o = .e8 e he) :
    IdentityPresentation
      (BinaryS16JointAxisRouting.criticalRouteE8
        H hH o j e he hp).axisSlot.slot := by
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
  let E := BinaryS16JointAxisRouting.localModelActionEquivOfEq hmodel
  let M := N.map E.toMonoidHom
  have hM : M.Normal := Subgroup.Normal.map hN E.toMonoidHom E.surjective
  refine ⟨.inl .e8,M,hM,?_⟩
  unfold BinaryS16JointAxisRouting.criticalRouteE8
  change @quotientIdentitySlot (.inl .e8) (N.map E.toMonoidHom) hM =
    @quotientIdentitySlot (.inl .e8) M hM
  rfl

/-- The canonical-axis wrapper preserves the fixed proper degree-eight slot. -/
theorem positiveRouteC8_slot_eq_exceptional
    (o : OrbitProfileFromOrbits.Orbit H)
    (j : Fin ((data H hH).multiplicity o))
    (W : BinaryDegreeEightNormalizerSaturatedDirect.OrbitWitness H)
    (hpoint : Quotient.mk'' W.point = o)
    (R : DegreeEightRoute W.action W.axis)
    (hp : profile H hH o = .carrier8 W hpoint R)
    (e : Exceptional)
    (he : degreeEightProperKind R.tag = some e) :
    (BinaryS16JointAxisRouting.positiveRouteC8
      H hH o j W hpoint R hp).axisSlot.slot = exceptionalSlot e := by
  rw [BinaryS16JointAxisRouting.positiveRouteC8_axisSlot_slot]
  exact degreeEightRoute_slot_eq_exceptional R e he

/-- The canonical-axis wrapper preserves the fixed proper degree-sixteen
slot. -/
theorem positiveRouteC16_slot_eq_exceptional
    (o : OrbitProfileFromOrbits.Orbit H)
    (j : Fin ((data H hH).multiplicity o))
    (W : BinaryDegree16PhysicalAnalyticClosure.OrbitWitness H)
    (hpoint : Quotient.mk'' W.point = o)
    (R : DegreeSixteenRoute W.action W.axis)
    (hp : profile H hH o = .carrier16 W hpoint R)
    (e : Exceptional)
    (he : degreeSixteenProperKind R.tag = some e) :
    (BinaryS16JointAxisRouting.positiveRouteC16
      H hH o j W hpoint R hp).axisSlot.slot = exceptionalSlot e := by
  rw [BinaryS16JointAxisRouting.positiveRouteC16_axisSlot_slot]
  exact degreeSixteenRoute_slot_eq_exceptional R e he

/-! ## Certificate-level and canonical-word access -/

/-- A certificate with a proper-carrier discriminator routes to the
corresponding literal exceptional slot. -/
theorem routeCertificate_slot_eq_exceptional
    {n : ℕ}
    (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : BinaryS16CanonicalCarrierProfile.ResidualSector H)
    (q : Σ o, Fin ((data H hH).multiplicity o))
    (cert : OrbitCertificate H q.1)
    (hp : profile H hH q.1 = cert)
    (e : Exceptional)
    (he : certificateProperKind cert = some e) :
    (BinaryS16JointAxisRouting.routeCertificate
      H hH q cert hp).axisSlot.slot = exceptionalSlot e := by
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
      unfold BinaryS16JointAxisRouting.routeCertificate
      exact positiveRouteC8_slot_eq_exceptional
        H hH q.1 q.2 W hpoint R hp e he
  | carrier16 W hpoint R =>
      unfold BinaryS16JointAxisRouting.routeCertificate
      exact positiveRouteC16_slot_eq_exceptional
        H hH q.1 q.2 W hpoint R hp e he

/-- A certificate without a proper-carrier discriminator routes to a literal
quotient-identity slot.  This is stronger than merely recording the absence
of a proper tag: it exposes the source kind, the retained normal axis, and the
dependent quotient presentation consumed by reverse identity naturality. -/
def routeCertificate_identityPresentation
    {n : ℕ}
    (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : BinaryS16CanonicalCarrierProfile.ResidualSector H)
    (q : Σ o, Fin ((data H hH).multiplicity o))
    (cert : OrbitCertificate H q.1)
    (hp : profile H hH q.1 = cert)
    (he : certificateProperKind cert = none) :
    IdentityPresentation
      (BinaryS16JointAxisRouting.routeCertificate
        H hH q cert hp).axisSlot.slot := by
  cases cert with
  | c2 e image =>
      exact criticalRouteC2_identityPresentation H hH q.1 q.2 e image hp
  | v4 e image =>
      exact criticalRouteV4_identityPresentation H hH q.1 q.2 e image hp
  | d8 e image =>
      exact criticalRouteD8_identityPresentation H hH q.1 q.2 e image hp
  | e8 e image =>
      exact criticalRouteE8_identityPresentation H hH q.1 q.2 e image hp
  | cyclicFour W hpoint R =>
      exact IdentityPresentation.cast
        (BinaryS16JointAxisRouting.positiveRouteC4_axisSlot_slot
          H hH q.1 q.2 W hpoint R hp).symm
        (degreeFourRoute_identityPresentation R)
  | carrier8 W hpoint R =>
      exact IdentityPresentation.cast
        (BinaryS16JointAxisRouting.positiveRouteC8_axisSlot_slot
          H hH q.1 q.2 W hpoint R hp).symm
        (degreeEightRoute_identityPresentation R he)
  | carrier16 W hpoint R =>
      exact IdentityPresentation.cast
        (BinaryS16JointAxisRouting.positiveRouteC16_axisSlot_slot
          H hH q.1 q.2 W hpoint R hp).symm
        (degreeSixteenRoute_identityPresentation R he)

/-- The optional proper-carrier kind attached to one literal source orbit.
`none` includes every quotient-identity route; `some e` is one of the four
fixed proper carriers. -/
def properKindAt
    {N : ℕ}
    (H : Subgroup (Equiv.Perm (Fin (2 * N))))
    (hH : BinaryS16CanonicalCarrierProfile.ResidualSector H)
    (o : OrbitProfileFromOrbits.Orbit H) : Option Exceptional :=
  (BinaryS16CanonicalMixedBlockTable.recordAt H hH o).bind properKind

/-- Reading the proper kind from the mixed record agrees with reading it
from the unique certificate which supplied that record. -/
theorem properKindAt_eq_certificateProperKind
    {N : ℕ}
    (H : Subgroup (Equiv.Perm (Fin (2 * N))))
    (hH : BinaryS16CanonicalCarrierProfile.ResidualSector H)
    (o : OrbitProfileFromOrbits.Orbit H) :
    properKindAt H hH o =
      certificateProperKind (profile H hH o) := by
  generalize hp : profile H hH o = cert
  cases cert <;>
    simp [properKindAt,BinaryS16CanonicalMixedBlockTable.recordAt,
      BinaryS16CanonicalMixedBlockTable.recordOfCertificate,hp,properKind,
      certificateProperKind]

/-- The complete canonical word has only two route shapes at each occurrence:
one of the four literal proper carriers, or a route whose proper discriminator
is absent.  The latter is exactly the quotient-identity side to which
`BinaryCarrierIdentitySlotNaturality` applies. -/
theorem axisRouting_proper_or_noProper
    {N : ℕ}
    (H : Subgroup (Equiv.Perm (Fin (2 * N))))
    (hH : BinaryS16CanonicalCarrierProfile.ResidualSector H)
    (q : Σ o, Fin ((data H hH).multiplicity o)) :
    (∃ e : Exceptional,
      properKindAt H hH q.1 = some e ∧
      (BinaryS16JointAxisRouting.axisRouting H hH q).axisSlot.slot =
        exceptionalSlot e) ∨
    properKindAt H hH q.1 = none := by
  rw [properKindAt_eq_certificateProperKind]
  generalize hp : profile H hH q.1 = cert
  cases hkind : certificateProperKind cert with
  | none => exact Or.inr rfl
  | some e =>
      left
      refine ⟨e,rfl,?_⟩
      unfold BinaryS16JointAxisRouting.axisRouting
      simpa only [hp] using
        routeCertificate_slot_eq_exceptional H hH q cert hp e hkind

/-- Every canonical occurrence has exactly the route shape needed by the
cross-variable decoder: one of the four fixed exceptional carriers, or an
explicit quotient-identity presentation retaining its normal axis. -/
theorem axisRouting_proper_or_identity
    {N : ℕ}
    (H : Subgroup (Equiv.Perm (Fin (2 * N))))
    (hH : BinaryS16CanonicalCarrierProfile.ResidualSector H)
    (q : Σ o, Fin ((data H hH).multiplicity o)) :
    ( ∃ e : Exceptional,
      properKindAt H hH q.1 = some e ∧
      (BinaryS16JointAxisRouting.axisRouting H hH q).axisSlot.slot =
        exceptionalSlot e) ∨
    Nonempty (IdentityPresentation
      (BinaryS16JointAxisRouting.axisRouting H hH q).axisSlot.slot) := by
  rw [properKindAt_eq_certificateProperKind]
  generalize hp : profile H hH q.1 = cert
  cases hkind : certificateProperKind cert with
  | some e =>
      left
      refine ⟨e,rfl,?_⟩
      unfold BinaryS16JointAxisRouting.axisRouting
      simpa only [hp] using
        routeCertificate_slot_eq_exceptional H hH q cert hp e hkind
  | none =>
      right
      refine ⟨?_⟩
      unfold BinaryS16JointAxisRouting.axisRouting
      simpa only [hp] using
        routeCertificate_identityPresentation H hH q cert hp hkind

/-- Direct accessor for the identity half of the route dichotomy. -/
def axisRouting_identityPresentation_of_properKindAt_eq_none
    {N : ℕ}
    (H : Subgroup (Equiv.Perm (Fin (2 * N))))
    (hH : BinaryS16CanonicalCarrierProfile.ResidualSector H)
    (q : Σ o, Fin ((data H hH).multiplicity o))
    (hkind : properKindAt H hH q.1 = none) :
    IdentityPresentation
      (BinaryS16JointAxisRouting.axisRouting H hH q).axisSlot.slot := by
  rw [properKindAt_eq_certificateProperKind] at hkind
  unfold BinaryS16JointAxisRouting.axisRouting
  exact routeCertificate_identityPresentation H hH q
    (profile H hH q.1) rfl hkind


end SymmetricSubgroupAsymptotics.BinaryS16RouteSlotSkeleton

end
