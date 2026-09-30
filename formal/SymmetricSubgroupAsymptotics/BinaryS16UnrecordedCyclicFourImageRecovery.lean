import SymmetricSubgroupAsymptotics.BinaryS16UnrecordedCyclicFourRecovery
import SymmetricSubgroupAsymptotics.BinaryS16UnrecordedOrbitImageRecoveryCore

/-!
# Complete restriction image on the unrecorded cyclic-four branch
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16UnrecordedCyclicFourImageRecovery

open SymmetricSubgroupAsymptotics
open BinaryCarrierProfileTransport
open BinaryCarrierS16TaggedPositiveRoutes
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
variable (C : SupportIndex N)

/-- The complete target restriction on an unrecorded cyclic-four orbit is
the original restriction image.  The proof retains the registry chart from
the same `DegreeFourRoute`; thus no action classifier is chosen a second
time. -/
theorem cyclicFour_sourceOrbitImage_is_targetOrbitImage
    (A : BinaryS16DirectPhysicalTarget.Actual C)
    (o : OrbitProfileFromOrbits.Orbit (subgroup C A))
    (W : SmallOrbitWitness 4 (subgroup C A))
    (hpoint : Quotient.mk'' W.point = o)
    (R : DegreeFourRoute W)
    (hp : profile (subgroup C A) (residualSector C A) o =
      OrbitCertificate.cyclicFour W hpoint R) :
    ∃ p : OrbitProfileFromOrbits.Orbit (targetSubgroup C A),
      ∃ hp : p.orbit = o.orbit,
        relabelSubgroup (Equiv.setCongr hp)
            (OrbitProfileFromOrbits.orbitImage (targetSubgroup C A) p) =
          OrbitProfileFromOrbits.orbitImage (subgroup C A) o := by
  let H := subgroup C A
  let hH := residualSector C A
  generalize hprof : profile H hH o = cert at hp
  cases cert with
  | cyclicFour W' hpoint' R' =>
    have hfull : OrbitProfileFullOn mixtureAction
        (BinaryS16FusionNaturalPointChart.pointChart H hH)
        (targetSubgroup C A) := by
      simpa only [H,hH,targetSubgroup] using targetSubgroup_full C A
    let j : Fin ((BinaryS16JointOrbitData.data H hH).multiplicity o) :=
      ⟨0,by simp⟩
    let q : Occurrence H hH := ⟨o,j⟩
    have hslot : RouteSlot H hH q =
        (BinaryS16JointAxisRouting.routeCertificate H hH q
          (OrbitCertificate.cyclicFour W' hpoint' R') hprof).axisSlot.slot :=
      routeSlot_eq_of_profile H hH q
        (OrbitCertificate.cyclicFour W' hpoint' R') hprof
    have hslotPhysical : RouteSlot H hH q = R'.certified.axisSlot.slot :=
      hslot.trans (BinaryS16JointAxisRouting.positiveRouteC4_axisSlot_slot
        H hH o j W' hpoint' R' hprof)
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
    have hc : (RouteSlot H hH q).color c = .inr none := by
      apply slot_color_eq_of_eq hslotPhysical c
      intro d
      unfold BinaryCarrierS16TaggedPositiveRoutes.DegreeFourRoute.certified at d ⊢
      unfold BinaryCarrierCertifiedRetention.CertifiedPositiveAxisSlot.ofCertificate at d ⊢
      unfold BinaryS16CanonicalCarrierProfile.SmallOrbitWitness.quotientIdentityAxisSlot at d ⊢
      unfold BinaryCarrierMenuSlots.quotientIdentitySlot at d ⊢
      unfold BinaryCarrierMenuSlots.identitySlot at d ⊢
      rfl
    let castPoint : mixturePoints ((RouteSlot H hH q).color c) ≃
        mixturePoints (.inr none) := Equiv.cast (congrArg mixturePoints hc)
    let localChart : Fin 4 ≃ o.orbit :=
      (BinaryS16JointOrbitData.certificateLocalModel H
        (.cyclicFour W' hpoint' R')).chart.pointEquiv
    let sourceChart : mixturePoints ((RouteSlot H hH q).color c) ≃ o.orbit :=
      (castPoint.trans R'.e).trans localChart
    have hsource : relabelSubgroup sourceChart
        (mixtureAction ((RouteSlot H hH q).color c)) =
        OrbitProfileFromOrbits.orbitImage H o := by
      calc
        relabelSubgroup sourceChart
            (mixtureAction ((RouteSlot H hH q).color c)) =
            relabelSubgroup localChart
              (relabelSubgroup R'.e
                (relabelSubgroup castPoint
                  (mixtureAction ((RouteSlot H hH q).color c)))) := by
          rw [relabelSubgroup_trans,relabelSubgroup_trans]
          rfl
        _ = relabelSubgroup localChart
            (relabelSubgroup R'.e (mixtureAction (.inr none))) := by
          rw [relabelSubgroup_cast_index mixturePoints mixtureAction hc]
        _ = relabelSubgroup localChart W'.action := by rw [R'.action_eq]
        _ = OrbitProfileFromOrbits.orbitImage H o :=
          (BinaryS16JointOrbitData.certificateLocalModel H
            (.cyclicFour W' hpoint' R')).chart.image_eq
    have hpointChart (y : mixturePoints ((RouteSlot H hH q).color c)) :
        ((sourceChart y : o.orbit) : Fin (2 * N)) =
          BinaryS16FusionNaturalPointChart.assemble H hH
            ⟨q,BinaryS16FusionNaturalPointChart.slotChart H hH q ⟨c,y⟩⟩ := by
      rw [assemble_apply_localModelChart]
      simp only [sourceChart,localChart,Equiv.trans_apply]
      dsimp only [q]
      symm
      change ((((BinaryS16FusionNaturalPointChart.slotChart H hH ⟨o,j⟩).trans
        (BinaryS16JointOrbitData.localModel H hH o).chart.pointEquiv)
          ⟨c,y⟩ : o.orbit) : Fin (2 * N)) = _
      exact congrArg (fun z : o.orbit => (z : Fin (2 * N)))
        (BinaryS16FusionNaturalPointChart.slotChart_trans_localChart_apply_cyclicFour
          H hH ⟨o,j⟩ W' hpoint' R' hprof c hc y)
    exact targetOrbitImage_eq_sourceOrbitImage_of_uniqueCell
      H hH hfull q c (fun _ ↦ Subsingleton.elim _ _)
        (by rw [hc]; exact cyclicFour_transitive)
        sourceChart hsource hpointChart

  | c2 e he => cases hp
  | v4 e he => cases hp
  | d8 e he => cases hp
  | e8 e he => cases hp
  | carrier8 W hpoint R => cases hp
  | carrier16 W hpoint R => cases hp

end SymmetricSubgroupAsymptotics.BinaryS16UnrecordedCyclicFourImageRecovery

end
