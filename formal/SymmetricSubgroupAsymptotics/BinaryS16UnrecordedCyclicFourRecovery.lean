import SymmetricSubgroupAsymptotics.BinaryS16UnrecordedOrbitCell

/-!
# Recovering an unrecorded cyclic-four S16 source orbit

The cyclic-four certificate has one routed cell.  Fullness of the physical
target on the fusion-natural chart and transitivity of the regular
cyclic-four action therefore identify that cell with the complete source
orbit.

The two carrier constructors are recorded by definition; short public
contradiction lemmas expose that fact for the remaining branches of the
unrecorded-orbit recovery theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16UnrecordedCyclicFourRecovery

open SymmetricSubgroupAsymptotics
open BinaryCarrierProfileTransport
open BinaryCarrierS16TaggedPositiveRoutes
open BinaryDegreeEightPhysicalDecoration
open BinaryDegreeEightSixteenPhysicalDecoration
open BinaryS16CanonicalCarrierProfile
open BinaryS16CanonicalMixedBlockTable
open BinaryS16DirectCertifiedOrbitProfile
open BinaryS16DirectFixedSupportClosure
open BinaryS16DirectPhysicalEncoding
open BinaryS16DirectPhysicalTarget
open BinaryS16TargetOrbitAccessor
open BinaryS16UnrecordedOrbitCell

variable {N : ℕ}
variable (C : SupportIndex N)

/-- A source orbit whose retained certificate is the cyclic-four constructor
is a literal orbit of the explicit relabelled raw target subgroup. -/
theorem cyclicFour_sourceOrbit_is_targetOrbit
    (A : BinaryS16DirectPhysicalTarget.Actual C)
    (o : OrbitProfileFromOrbits.Orbit (subgroup C A))
    (W : SmallOrbitWitness 4 (subgroup C A))
    (hpoint : Quotient.mk'' W.point = o)
    (R : DegreeFourRoute W)
    (hp : profile (subgroup C A) (residualSector C A) o =
      OrbitCertificate.cyclicFour W hpoint R) :
    ∃ z : Fin (2 * N),
      MulAction.orbit (targetSubgroup C A) z = o.orbit := by
  let H := subgroup C A
  let hH := residualSector C A
  have hfull : OrbitProfileFullOn mixtureAction
      (BinaryS16FusionNaturalPointChart.pointChart H hH)
      (targetSubgroup C A) := by
    simpa only [H,hH,targetSubgroup] using targetSubgroup_full C A
  let j : Fin ((BinaryS16JointOrbitData.data H hH).multiplicity o) :=
    ⟨0,by simp⟩
  let q : Occurrence H hH := ⟨o,j⟩
  have hslot : RouteSlot H hH q =
      (BinaryS16JointAxisRouting.routeCertificate H hH q
        (OrbitCertificate.cyclicFour W hpoint R) hp).axisSlot.slot :=
    routeSlot_eq_of_profile H hH q
      (OrbitCertificate.cyclicFour W hpoint R) hp
  have hslotPhysical : RouteSlot H hH q = R.certified.axisSlot.slot :=
    hslot.trans (BinaryS16JointAxisRouting.positiveRouteC4_axisSlot_slot
      H hH o j W hpoint R hp)
  letI : Subsingleton (RouteSlot H hH q).Cells := by
    rw [hslotPhysical]
    unfold BinaryCarrierS16TaggedPositiveRoutes.DegreeFourRoute.certified
    unfold BinaryCarrierCertifiedRetention.CertifiedPositiveAxisSlot.ofCertificate
    unfold BinaryS16CanonicalCarrierProfile.SmallOrbitWitness.quotientIdentityAxisSlot
    unfold BinaryCarrierMenuSlots.quotientIdentitySlot
    unfold BinaryCarrierMenuSlots.identitySlot
    unfold BinaryCarrierCertifiedRetention.CertifiedSlot.ofCertificate
    dsimp
    infer_instance
  letI : Nonempty (RouteSlot H hH q).Cells := by
    rw [hslotPhysical]
    unfold BinaryCarrierS16TaggedPositiveRoutes.DegreeFourRoute.certified
    unfold BinaryCarrierCertifiedRetention.CertifiedPositiveAxisSlot.ofCertificate
    unfold BinaryS16CanonicalCarrierProfile.SmallOrbitWitness.quotientIdentityAxisSlot
    unfold BinaryCarrierMenuSlots.quotientIdentitySlot
    unfold BinaryCarrierMenuSlots.identitySlot
    unfold BinaryCarrierCertifiedRetention.CertifiedSlot.ofCertificate
    dsimp
    infer_instance
  let c : (RouteSlot H hH q).Cells := Classical.choice inferInstance
  apply targetOrbit_eq_sourceOrbit_of_uniqueCell H hH hfull q c
    (fun _ ↦ Subsingleton.elim _ _)
  have hc : (RouteSlot H hH q).color c = .inr none := by
    apply slot_color_eq_of_eq hslotPhysical c
    intro d
    unfold BinaryCarrierS16TaggedPositiveRoutes.DegreeFourRoute.certified at d ⊢
    unfold BinaryCarrierCertifiedRetention.CertifiedPositiveAxisSlot.ofCertificate at d ⊢
    unfold BinaryS16CanonicalCarrierProfile.SmallOrbitWitness.quotientIdentityAxisSlot at d ⊢
    unfold BinaryCarrierMenuSlots.quotientIdentitySlot at d ⊢
    unfold BinaryCarrierMenuSlots.identitySlot at d ⊢
    rfl
  rw [hc]
  exact cyclicFour_transitive

/-- A degree-eight carrier profile cannot have an absent mixed-table record. -/
theorem carrier8_profile_not_unrecorded
    (A : BinaryS16DirectPhysicalTarget.Actual C)
    (o : OrbitProfileFromOrbits.Orbit (subgroup C A))
    (W : BinaryDegreeEightNormalizerSaturatedDirect.OrbitWitness
      (subgroup C A))
    (hpoint : Quotient.mk'' W.point = o)
    (R : DegreeEightRoute W.action W.axis)
    (hp : profile (subgroup C A) (residualSector C A) o =
      OrbitCertificate.carrier8 W hpoint R)
    (hunrecorded : recordAt (subgroup C A) (residualSector C A) o = none) :
    False := by
  simpa [recordAt,recordOfCertificate,hp] using hunrecorded

/-- A degree-sixteen carrier profile cannot have an absent mixed-table
record. -/
theorem carrier16_profile_not_unrecorded
    (A : BinaryS16DirectPhysicalTarget.Actual C)
    (o : OrbitProfileFromOrbits.Orbit (subgroup C A))
    (W : BinaryDegree16PhysicalAnalyticClosure.OrbitWitness (subgroup C A))
    (hpoint : Quotient.mk'' W.point = o)
    (R : DegreeSixteenRoute W.action W.axis)
    (hp : profile (subgroup C A) (residualSector C A) o =
      OrbitCertificate.carrier16 W hpoint R)
    (hunrecorded : recordAt (subgroup C A) (residualSector C A) o = none) :
    False := by
  simpa [recordAt,recordOfCertificate,hp] using hunrecorded

end SymmetricSubgroupAsymptotics.BinaryS16UnrecordedCyclicFourRecovery

end
