import SymmetricSubgroupAsymptotics.BinaryS16UnrecordedOrbitCell

/-!
# Recovering the unrecorded C2 and V4 source orbits

These public branch lemmas isolate the C2 and V4 cases of the unrecorded
source-orbit recovery theorem.  Each one exposes the chosen critical
certificate as a hypothesis and identifies the source orbit with a literal
orbit of the explicit relabelled raw target subgroup.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16UnrecordedC2V4Recovery

open SymmetricSubgroupAsymptotics
open BinaryCarrierProfileTransport
open BinaryDegreeEightPhysicalDecoration
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

/-- A source orbit carrying the critical C2 certificate is a literal orbit
of the explicit relabelled raw target subgroup. -/
theorem c2_sourceOrbit_is_targetOrbit
    (A : BinaryS16DirectPhysicalTarget.Actual C)
    (o : OrbitProfileFromOrbits.Orbit (subgroup C A))
    (e : criticalActionPoints .c2 ≃ o.orbit)
    (he : relabelSubgroup e (criticalActionSubgroup .c2) =
      OrbitProfileFromOrbits.orbitImage (subgroup C A) o)
    (hp : profile (subgroup C A) (residualSector C A) o =
      OrbitCertificate.c2 e he) :
    ∃ z : Fin (2 * N),
      MulAction.orbit (targetSubgroup C A) z = o.orbit := by
  let H := subgroup C A
  let hH := residualSector C A
  change profile H hH o = OrbitCertificate.c2 e he at hp
  have hfull : OrbitProfileFullOn mixtureAction
      (BinaryS16FusionNaturalPointChart.pointChart H hH)
      (targetSubgroup C A) := by
    simpa only [H,hH,targetSubgroup] using targetSubgroup_full C A
  let j : Fin ((BinaryS16JointOrbitData.data H hH).multiplicity o) :=
    ⟨0,by simp⟩
  let q : Occurrence H hH := ⟨o,j⟩
  have hslot : RouteSlot H hH q =
      (BinaryS16JointAxisRouting.routeCertificate H hH q
        (OrbitCertificate.c2 e he) hp).axisSlot.slot :=
    routeSlot_eq_of_profile H hH q (OrbitCertificate.c2 e he) hp
  letI : Subsingleton (RouteSlot H hH q).Cells := by
    rw [hslot]
    unfold BinaryS16JointAxisRouting.routeCertificate
    simp only
    unfold BinaryS16JointAxisRouting.criticalRouteC2
    simp
    unfold BinaryS16JointAxisRouting.criticalCertifiedSlot
    unfold BinaryCarrierMenuSlots.quotientIdentitySlot
    unfold BinaryCarrierMenuSlots.identitySlot
    unfold BinaryCarrierCertifiedRetention.CertifiedSlot.ofCertificate
    dsimp
    infer_instance
  letI : Nonempty (RouteSlot H hH q).Cells := by
    rw [hslot]
    unfold BinaryS16JointAxisRouting.routeCertificate
    simp only
    unfold BinaryS16JointAxisRouting.criticalRouteC2
    simp
    unfold BinaryS16JointAxisRouting.criticalCertifiedSlot
    unfold BinaryCarrierMenuSlots.quotientIdentitySlot
    unfold BinaryCarrierMenuSlots.identitySlot
    unfold BinaryCarrierCertifiedRetention.CertifiedSlot.ofCertificate
    dsimp
    infer_instance
  let c : (RouteSlot H hH q).Cells := Classical.choice inferInstance
  apply targetOrbit_eq_sourceOrbit_of_uniqueCell H hH hfull q c
    (fun _ ↦ Subsingleton.elim _ _)
  have hc : (RouteSlot H hH q).color c = .inl .c2 := by
    apply slot_color_eq_of_eq hslot c
    intro d
    unfold BinaryS16JointAxisRouting.routeCertificate at d ⊢
    simp only at d ⊢
    unfold BinaryS16JointAxisRouting.criticalRouteC2 at d ⊢
    simp at d ⊢
    unfold BinaryS16JointAxisRouting.criticalCertifiedSlot at d ⊢
    unfold BinaryCarrierMenuSlots.quotientIdentitySlot at d ⊢
    unfold BinaryCarrierMenuSlots.identitySlot at d ⊢
    rfl
  rw [hc]
  exact criticalAction_permutationTransitive .c2

/-- A source orbit carrying the critical V4 certificate is a literal orbit
of the explicit relabelled raw target subgroup. -/
theorem v4_sourceOrbit_is_targetOrbit
    (A : BinaryS16DirectPhysicalTarget.Actual C)
    (o : OrbitProfileFromOrbits.Orbit (subgroup C A))
    (e : criticalActionPoints .v4 ≃ o.orbit)
    (he : relabelSubgroup e (criticalActionSubgroup .v4) =
      OrbitProfileFromOrbits.orbitImage (subgroup C A) o)
    (hp : profile (subgroup C A) (residualSector C A) o =
      OrbitCertificate.v4 e he) :
    ∃ z : Fin (2 * N),
      MulAction.orbit (targetSubgroup C A) z = o.orbit := by
  let H := subgroup C A
  let hH := residualSector C A
  change profile H hH o = OrbitCertificate.v4 e he at hp
  have hfull : OrbitProfileFullOn mixtureAction
      (BinaryS16FusionNaturalPointChart.pointChart H hH)
      (targetSubgroup C A) := by
    simpa only [H,hH,targetSubgroup] using targetSubgroup_full C A
  let j : Fin ((BinaryS16JointOrbitData.data H hH).multiplicity o) :=
    ⟨0,by simp⟩
  let q : Occurrence H hH := ⟨o,j⟩
  have hslot : RouteSlot H hH q =
      (BinaryS16JointAxisRouting.routeCertificate H hH q
        (OrbitCertificate.v4 e he) hp).axisSlot.slot :=
    routeSlot_eq_of_profile H hH q (OrbitCertificate.v4 e he) hp
  letI : Subsingleton (RouteSlot H hH q).Cells := by
    rw [hslot]
    unfold BinaryS16JointAxisRouting.routeCertificate
    simp only
    unfold BinaryS16JointAxisRouting.criticalRouteV4
    simp
    unfold BinaryS16JointAxisRouting.criticalCertifiedSlot
    unfold BinaryCarrierMenuSlots.quotientIdentitySlot
    unfold BinaryCarrierMenuSlots.identitySlot
    unfold BinaryCarrierCertifiedRetention.CertifiedSlot.ofCertificate
    dsimp
    infer_instance
  letI : Nonempty (RouteSlot H hH q).Cells := by
    rw [hslot]
    unfold BinaryS16JointAxisRouting.routeCertificate
    simp only
    unfold BinaryS16JointAxisRouting.criticalRouteV4
    simp
    unfold BinaryS16JointAxisRouting.criticalCertifiedSlot
    unfold BinaryCarrierMenuSlots.quotientIdentitySlot
    unfold BinaryCarrierMenuSlots.identitySlot
    unfold BinaryCarrierCertifiedRetention.CertifiedSlot.ofCertificate
    dsimp
    infer_instance
  let c : (RouteSlot H hH q).Cells := Classical.choice inferInstance
  apply targetOrbit_eq_sourceOrbit_of_uniqueCell H hH hfull q c
    (fun _ ↦ Subsingleton.elim _ _)
  have hc : (RouteSlot H hH q).color c = .inl .v4 := by
    apply slot_color_eq_of_eq hslot c
    intro d
    unfold BinaryS16JointAxisRouting.routeCertificate at d ⊢
    simp only at d ⊢
    unfold BinaryS16JointAxisRouting.criticalRouteV4 at d ⊢
    simp at d ⊢
    unfold BinaryS16JointAxisRouting.criticalCertifiedSlot at d ⊢
    unfold BinaryCarrierMenuSlots.quotientIdentitySlot at d ⊢
    unfold BinaryCarrierMenuSlots.identitySlot at d ⊢
    rfl
  rw [hc]
  exact criticalAction_permutationTransitive .v4

end SymmetricSubgroupAsymptotics.BinaryS16UnrecordedC2V4Recovery

end
