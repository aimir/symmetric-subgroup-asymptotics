import SymmetricSubgroupAsymptotics.BinaryS16UnrecordedOrbitD8E8
import SymmetricSubgroupAsymptotics.BinaryS16UnrecordedOrbitImageRecoveryCore

/-!
# Complete restriction images on the unrecorded D8 and E8 branches
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16UnrecordedD8E8ImageRecovery

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
open BinaryS16UnrecordedOrbitImageAccessor
open BinaryS16UnrecordedOrbitImageRecoveryCore

variable {N : ℕ}

/-- The complete target restriction on an unrecorded D8 orbit is its
original restriction image. -/
theorem d8_sourceOrbitImage_is_targetOrbitImage
    (C : SupportIndex N)
    (A : BinaryS16DirectPhysicalTarget.Actual C)
    (o : OrbitProfileFromOrbits.Orbit (subgroup C A))
    {e : criticalActionPoints .d8 ≃ o.orbit}
    {he : relabelSubgroup e (criticalActionSubgroup .d8) =
      OrbitProfileFromOrbits.orbitImage (subgroup C A) o}
    (hp : profile (subgroup C A) (residualSector C A) o =
      OrbitCertificate.d8 e he) :
    ∃ p : OrbitProfileFromOrbits.Orbit (targetSubgroup C A),
      ∃ hp : p.orbit = o.orbit,
        relabelSubgroup (Equiv.setCongr hp)
            (OrbitProfileFromOrbits.orbitImage (targetSubgroup C A) p) =
          OrbitProfileFromOrbits.orbitImage (subgroup C A) o := by
  let H := subgroup C A
  let hH := residualSector C A
  generalize hprof : profile H hH o = cert at hp
  cases cert with
  | d8 e' he' =>
    have hfull : OrbitProfileFullOn mixtureAction
        (BinaryS16FusionNaturalPointChart.pointChart H hH)
        (targetSubgroup C A) := by
      simpa only [H,hH,targetSubgroup] using targetSubgroup_full C A
    let j : Fin ((BinaryS16JointOrbitData.data H hH).multiplicity o) :=
      ⟨0,by simp [H,hH,hprof]⟩
    let q : Occurrence H hH := ⟨o,j⟩
    have hslot : RouteSlot H hH q =
        (BinaryS16JointAxisRouting.routeCertificate H hH q
          (OrbitCertificate.d8 e' he') hprof).axisSlot.slot :=
      routeSlot_eq_of_profile H hH q (OrbitCertificate.d8 e' he') hprof
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
    let castPoint : mixturePoints ((RouteSlot H hH q).color c) ≃
        criticalActionPoints .d8 := Equiv.cast (congrArg mixturePoints hc)
    let sourceChart : mixturePoints ((RouteSlot H hH q).color c) ≃ o.orbit :=
      castPoint.trans e'
    have hsource : relabelSubgroup sourceChart
        (mixtureAction ((RouteSlot H hH q).color c)) =
        OrbitProfileFromOrbits.orbitImage H o := by
      calc
        relabelSubgroup sourceChart
            (mixtureAction ((RouteSlot H hH q).color c)) =
            relabelSubgroup e'
              (relabelSubgroup castPoint
                (mixtureAction ((RouteSlot H hH q).color c))) :=
          (relabelSubgroup_trans castPoint e' _).symm
        _ = relabelSubgroup e' (criticalActionSubgroup .d8) := by
          change relabelSubgroup e'
              (relabelSubgroup (Equiv.cast (congrArg mixturePoints hc))
                (mixtureAction ((RouteSlot H hH q).color c))) = _
          rw [relabelSubgroup_cast_index mixturePoints mixtureAction hc]
          rfl
        _ = OrbitProfileFromOrbits.orbitImage H o := he'
    have hpoint (y : mixturePoints ((RouteSlot H hH q).color c)) :
        ((sourceChart y : o.orbit) : Fin (2 * N)) =
          BinaryS16FusionNaturalPointChart.assemble H hH
            ⟨q,BinaryS16FusionNaturalPointChart.slotChart H hH q ⟨c,y⟩⟩ := by
      rw [assemble_apply_localModelChart]
      simp only [sourceChart,Equiv.trans_apply]
      dsimp only [q]
      symm
      change ((((BinaryS16FusionNaturalPointChart.slotChart H hH ⟨o,j⟩).trans
        (BinaryS16JointOrbitData.localModel H hH o).chart.pointEquiv)
          ⟨c,y⟩ : o.orbit) : Fin (2 * N)) = _
      exact congrArg (fun z : o.orbit => (z : Fin (2 * N)))
        (BinaryS16FusionNaturalPointChart.slotChart_trans_localChart_apply_d8
          H hH ⟨o,j⟩ e' he' hprof c hc y)
    exact targetOrbitImage_eq_sourceOrbitImage_of_uniqueCell
      H hH hfull q c (fun _ ↦ Subsingleton.elim _ _)
        (by rw [hc]; exact criticalAction_permutationTransitive .d8)
        sourceChart hsource hpoint

  | c2 e he => cases hp
  | v4 e he => cases hp
  | e8 e he => cases hp
  | cyclicFour W hpoint R => cases hp
  | carrier8 W hpoint R => cases hp
  | carrier16 W hpoint R => cases hp

/-- The complete target restriction on an unrecorded E8 orbit is its
original restriction image. -/
theorem e8_sourceOrbitImage_is_targetOrbitImage
    (C : SupportIndex N)
    (A : BinaryS16DirectPhysicalTarget.Actual C)
    (o : OrbitProfileFromOrbits.Orbit (subgroup C A))
    {e : criticalActionPoints .e8 ≃ o.orbit}
    {he : relabelSubgroup e (criticalActionSubgroup .e8) =
      OrbitProfileFromOrbits.orbitImage (subgroup C A) o}
    (hp : profile (subgroup C A) (residualSector C A) o =
      OrbitCertificate.e8 e he) :
    ∃ p : OrbitProfileFromOrbits.Orbit (targetSubgroup C A),
      ∃ hp : p.orbit = o.orbit,
        relabelSubgroup (Equiv.setCongr hp)
            (OrbitProfileFromOrbits.orbitImage (targetSubgroup C A) p) =
          OrbitProfileFromOrbits.orbitImage (subgroup C A) o := by
  let H := subgroup C A
  let hH := residualSector C A
  generalize hprof : profile H hH o = cert at hp
  cases cert with
  | e8 e' he' =>
    have hfull : OrbitProfileFullOn mixtureAction
        (BinaryS16FusionNaturalPointChart.pointChart H hH)
        (targetSubgroup C A) := by
      simpa only [H,hH,targetSubgroup] using targetSubgroup_full C A
    let j : Fin ((BinaryS16JointOrbitData.data H hH).multiplicity o) :=
      ⟨0,by simp [H,hH,hprof]⟩
    let q : Occurrence H hH := ⟨o,j⟩
    have hslot : RouteSlot H hH q =
        (BinaryS16JointAxisRouting.routeCertificate H hH q
          (OrbitCertificate.e8 e' he') hprof).axisSlot.slot :=
      routeSlot_eq_of_profile H hH q (OrbitCertificate.e8 e' he') hprof
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
    let castPoint : mixturePoints ((RouteSlot H hH q).color c) ≃
        criticalActionPoints .e8 := Equiv.cast (congrArg mixturePoints hc)
    let sourceChart : mixturePoints ((RouteSlot H hH q).color c) ≃ o.orbit :=
      castPoint.trans e'
    have hsource : relabelSubgroup sourceChart
        (mixtureAction ((RouteSlot H hH q).color c)) =
        OrbitProfileFromOrbits.orbitImage H o := by
      calc
        relabelSubgroup sourceChart
            (mixtureAction ((RouteSlot H hH q).color c)) =
            relabelSubgroup e'
              (relabelSubgroup castPoint
                (mixtureAction ((RouteSlot H hH q).color c))) :=
          (relabelSubgroup_trans castPoint e' _).symm
        _ = relabelSubgroup e' (criticalActionSubgroup .e8) := by
          change relabelSubgroup e'
              (relabelSubgroup (Equiv.cast (congrArg mixturePoints hc))
                (mixtureAction ((RouteSlot H hH q).color c))) = _
          rw [relabelSubgroup_cast_index mixturePoints mixtureAction hc]
          rfl
        _ = OrbitProfileFromOrbits.orbitImage H o := he'
    have hpoint (y : mixturePoints ((RouteSlot H hH q).color c)) :
        ((sourceChart y : o.orbit) : Fin (2 * N)) =
          BinaryS16FusionNaturalPointChart.assemble H hH
            ⟨q,BinaryS16FusionNaturalPointChart.slotChart H hH q ⟨c,y⟩⟩ := by
      rw [assemble_apply_localModelChart]
      simp only [sourceChart,Equiv.trans_apply]
      dsimp only [q]
      symm
      change ((((BinaryS16FusionNaturalPointChart.slotChart H hH ⟨o,j⟩).trans
        (BinaryS16JointOrbitData.localModel H hH o).chart.pointEquiv)
          ⟨c,y⟩ : o.orbit) : Fin (2 * N)) = _
      exact congrArg (fun z : o.orbit => (z : Fin (2 * N)))
        (BinaryS16FusionNaturalPointChart.slotChart_trans_localChart_apply_e8
          H hH ⟨o,j⟩ e' he' hprof c hc y)
    exact targetOrbitImage_eq_sourceOrbitImage_of_uniqueCell
      H hH hfull q c (fun _ ↦ Subsingleton.elim _ _)
        (by rw [hc]; exact criticalAction_permutationTransitive .e8)
        sourceChart hsource hpoint

  | c2 e he => cases hp
  | v4 e he => cases hp
  | d8 e he => cases hp
  | cyclicFour W hpoint R => cases hp
  | carrier8 W hpoint R => cases hp
  | carrier16 W hpoint R => cases hp

end SymmetricSubgroupAsymptotics.BinaryS16UnrecordedD8E8ImageRecovery

end
