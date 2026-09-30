import SymmetricSubgroupAsymptotics.BinaryS16UnrecordedOrbitCell

/-!
# The D8 and E8 unrecorded S16 source-orbit branches

These public helpers isolate the two exceptional critical-action branches of
`BinaryS16UnrecordedOrbitRecovery.unrecorded_sourceOrbit_is_targetOrbit`.
Each branch is a one-cell route, so exact fullness of the physical target
identifies that target orbit with the original source orbit.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16UnrecordedOrbitD8E8

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

/-- A source orbit carrying the critical D8 profile is a literal orbit of the
explicit relabelled raw target subgroup. -/
theorem d8_sourceOrbit_is_targetOrbit
    (C : SupportIndex N)
    (A : BinaryS16DirectPhysicalTarget.Actual C)
    (o : OrbitProfileFromOrbits.Orbit (subgroup C A))
    {e : criticalActionPoints .d8 ≃ o.orbit}
    {he : relabelSubgroup e (criticalActionSubgroup .d8) =
      OrbitProfileFromOrbits.orbitImage (subgroup C A) o}
    (hp : profile (subgroup C A) (residualSector C A) o = OrbitCertificate.d8 e he) :
    ∃ z : Fin (2 * N),
      MulAction.orbit (targetSubgroup C A) z = o.orbit := by
  let H := subgroup C A
  let hH := residualSector C A
  have hfull : OrbitProfileFullOn mixtureAction
      (BinaryS16FusionNaturalPointChart.pointChart H hH)
      (targetSubgroup C A) := by
    simpa only [H,hH,targetSubgroup] using targetSubgroup_full C A
  let j : Fin ((BinaryS16JointOrbitData.data H hH).multiplicity o) :=
    ⟨0,by simp [H,hH,hp]⟩
  let q : Occurrence H hH := ⟨o,j⟩
  have hslot : RouteSlot H hH q =
      (BinaryS16JointAxisRouting.routeCertificate H hH q
        (OrbitCertificate.d8 e he) hp).axisSlot.slot :=
    routeSlot_eq_of_profile H hH q (OrbitCertificate.d8 e he) hp
  letI : Subsingleton (RouteSlot H hH q).Cells := by
    rw [hslot]
    unfold BinaryS16JointAxisRouting.routeCertificate
    simp only
    unfold BinaryS16JointAxisRouting.criticalRouteD8
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
    unfold BinaryS16JointAxisRouting.criticalRouteD8
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
  have hc : (RouteSlot H hH q).color c = .inl .d8 := by
    apply slot_color_eq_of_eq hslot c
    intro d
    unfold BinaryS16JointAxisRouting.routeCertificate at d ⊢
    simp only at d ⊢
    unfold BinaryS16JointAxisRouting.criticalRouteD8 at d ⊢
    simp at d ⊢
    unfold BinaryS16JointAxisRouting.criticalCertifiedSlot at d ⊢
    unfold BinaryCarrierMenuSlots.quotientIdentitySlot at d ⊢
    unfold BinaryCarrierMenuSlots.identitySlot at d ⊢
    rfl
  rw [hc]
  exact criticalAction_permutationTransitive .d8

/-- A source orbit carrying the critical E8 profile is a literal orbit of the
explicit relabelled raw target subgroup. -/
theorem e8_sourceOrbit_is_targetOrbit
    (C : SupportIndex N)
    (A : BinaryS16DirectPhysicalTarget.Actual C)
    (o : OrbitProfileFromOrbits.Orbit (subgroup C A))
    {e : criticalActionPoints .e8 ≃ o.orbit}
    {he : relabelSubgroup e (criticalActionSubgroup .e8) =
      OrbitProfileFromOrbits.orbitImage (subgroup C A) o}
    (hp : profile (subgroup C A) (residualSector C A) o = OrbitCertificate.e8 e he) :
    ∃ z : Fin (2 * N),
      MulAction.orbit (targetSubgroup C A) z = o.orbit := by
  let H := subgroup C A
  let hH := residualSector C A
  have hfull : OrbitProfileFullOn mixtureAction
      (BinaryS16FusionNaturalPointChart.pointChart H hH)
      (targetSubgroup C A) := by
    simpa only [H,hH,targetSubgroup] using targetSubgroup_full C A
  let j : Fin ((BinaryS16JointOrbitData.data H hH).multiplicity o) :=
    ⟨0,by simp [H,hH,hp]⟩
  let q : Occurrence H hH := ⟨o,j⟩
  have hslot : RouteSlot H hH q =
      (BinaryS16JointAxisRouting.routeCertificate H hH q
        (OrbitCertificate.e8 e he) hp).axisSlot.slot :=
    routeSlot_eq_of_profile H hH q (OrbitCertificate.e8 e he) hp
  letI : Subsingleton (RouteSlot H hH q).Cells := by
    rw [hslot]
    unfold BinaryS16JointAxisRouting.routeCertificate
    simp only
    unfold BinaryS16JointAxisRouting.criticalRouteE8
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
    unfold BinaryS16JointAxisRouting.criticalRouteE8
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
  have hc : (RouteSlot H hH q).color c = .inl .e8 := by
    apply slot_color_eq_of_eq hslot c
    intro d
    unfold BinaryS16JointAxisRouting.routeCertificate at d ⊢
    simp only at d ⊢
    unfold BinaryS16JointAxisRouting.criticalRouteE8 at d ⊢
    simp at d ⊢
    unfold BinaryS16JointAxisRouting.criticalCertifiedSlot at d ⊢
    unfold BinaryCarrierMenuSlots.quotientIdentitySlot at d ⊢
    unfold BinaryCarrierMenuSlots.identitySlot at d ⊢
    rfl
  rw [hc]
  exact criticalAction_permutationTransitive .e8

end SymmetricSubgroupAsymptotics.BinaryS16UnrecordedOrbitD8E8

end
