import SymmetricSubgroupAsymptotics.C3PhysicalOwnerFusionCover
import SymmetricSubgroupAsymptotics.Non2FirstOwnerPhysicalFrontier

/-!
# First-owner non-2 fusion charts for the high-C3 branches

The unfiltered cover of `C3PhysicalOwnerFusionCover` is strengthened here to
the exact complete-subgroup first-owner predicate used by the general non-2
recurrence.  The local predicate is proved on the deleted model by literal
reconstruction of the original physical subgroup.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace C3HighNestedCarrier

/-- A specified action chart for the orbit retained by a high-C3 witness
enters the owner-indexed non-2 family.  Keeping the chart visible lets later
consumers transport the normal high pair to this exact deleted action. -/
theorem Data.mem_non2FirstOwnerCanonicalFamily_forAction
    {r b w : ℕ}
    (Eligible : ∀ n, Fin r → Subgroup (Equiv.Perm (Fin n)) → Prop)
    (hEligible : DegreeNaturalOwnerMenu Eligible)
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)))
    (C : Data H)
    (hw : Nat.card C.orbit.orbit = w)
    (q : TernaryCyclic ⊕ Fin b ≃ Fin (b + 3))
    (hordinary : ¬ IsCriticalSubgroup (b + 3)
      (relabelSubgroup q (physicalSubgroup H)))
    (owner : Fin r)
    (howner : FirstOwned (Eligible (b + 3)) owner
      (relabelSubgroup q (physicalSubgroup H)))
    (i : Non2TransitiveActionClass (Fin w))
    (eO : Fin w ≃ C.orbit.orbit)
    (himage : relabelSubgroup eO i.representative =
      OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) C.orbit) :
    relabelSubgroup q (physicalSubgroup H) ∈
      FusionWidthCanonicalFamily
        (non2FirstOwnerAction w (owner, i)) (by
          have hwb := width_le H C.orbit hw
          omega)
        (non2FirstOwnerPredicate Eligible w (owner, i) (b + 3 - w)) := by
  have hwb : w ≤ b := width_le H C.orbit hw
  have hn : w ≤ b + 3 := by omega
  let K := relabelSubgroup (chart H C.orbit hw eO).symm
    (physicalSubgroup H)
  have hblock := FusionOrbitProfileChart.chart_preserves
    (physicalSubgroup H) (liftedOrbit H C.orbit)
      (pointEquiv H C.orbit eO) (complementEquiv H C.orbit hw)
  have hprojection := FusionOrbitProfileChart.chart_projection_eq
    (physicalSubgroup H) (liftedOrbit H C.orbit) i.representative
      (pointEquiv H C.orbit eO) (complementEquiv H C.orbit hw)
      (pointEquiv_image H C.orbit i.representative eO himage)
  have hrec := fusionDeletedModel_recovers i.representative K
    hblock hprojection
  have hlocal : non2FirstOwnerPredicate Eligible w (owner, i) (b + 3 - w)
      (fusionDeletedModel i.representative K) := by
    let r₀ : Fin w ⊕ Fin (b + 3 - w) ≃ Fin (w + (b + 3 - w)) :=
      finSumFinEquiv
    let e : Fin w ⊕ Fin (b + 3 - w) ≃ TernaryCyclic ⊕ Fin b :=
      chart H C.orbit hw eO
    let s : Fin (w + (b + 3 - w)) ≃ Fin (b + 3) :=
      r₀.symm.trans (e.trans q)
    let L : Subgroup (Equiv.Perm (Fin (w + (b + 3 - w)))) :=
      relabelSubgroup r₀ K
    have hs : relabelSubgroup s L =
        relabelSubgroup q (physicalSubgroup H) := by
      dsimp only [L]
      rw [relabelSubgroup_trans]
      have hrs : r₀.trans s = e.trans q := by
        apply Equiv.ext
        intro x
        change q (e (r₀.symm (r₀ x))) = q (e x)
        exact congrArg (fun y => q (e y)) (r₀.symm_apply_apply x)
      rw [hrs]
      dsimp only [K, e]
      rw [← relabelSubgroup_trans]
      exact congrArg (relabelSubgroup q)
        (relabelSubgroup_symm
          (chart H C.orbit hw eO).symm (physicalSubgroup H))
    have hordinaryL : ¬ IsCriticalSubgroup (w + (b + 3 - w)) L := by
      apply (ordinaryRemainder_relabel_equiv_iff
        (show w + (b + 3 - w) = b + 3 by omega) s L).mp
      rwa [hs]
    have hownerL : FirstOwned (Eligible (w + (b + 3 - w))) owner L := by
      have htransport := firstOwned_transport_iff
        (Eligible (w + (b + 3 - w))) (Eligible (b + 3))
        (relabelSubgroup s)
        (fun j M => (hEligible
          (show w + (b + 3 - w) = b + 3 by omega) s j M).symm)
        owner L
      apply htransport.mpr
      rwa [hs]
    have hphysical :
        relabelSubgroup r₀
          ((fusionDeletedModel i.representative K).map
            (fusionOrbitAction i.representative)) = L := by
      dsimp only [L]
      exact congrArg (relabelSubgroup r₀) hrec
    unfold non2FirstOwnerPredicate ordinaryFirstOwnerLocalPredicate
    simp only [non2FirstOwnerAction]
    constructor
    · unfold ordinaryRemainderFusionPredicate
      exact hphysical.symm ▸ hordinaryL
    · exact hphysical.symm ▸ hownerL
  exact mem_widthCanonicalFamily_of_relabel H C hw i.representative
    eO himage q
    (non2FirstOwnerPredicate Eligible w (owner, i) (b + 3 - w)) hlocal

/-- The orbit retained by a high-C3 witness enters the owner-indexed non-2
family.  First ownership and noncriticality are transported from the complete
physical subgroup to its exact deleted model; the complement is unchanged. -/
theorem Data.mem_non2FirstOwnerCanonicalFamily_atWidth
    {r b w : ℕ}
    (Eligible : ∀ n, Fin r → Subgroup (Equiv.Perm (Fin n)) → Prop)
    (hEligible : DegreeNaturalOwnerMenu Eligible)
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)))
    (C : Data H)
    (hw : Nat.card C.orbit.orbit = w)
    (q : TernaryCyclic ⊕ Fin b ≃ Fin (b + 3))
    (hordinary : ¬ IsCriticalSubgroup (b + 3)
      (relabelSubgroup q (physicalSubgroup H)))
    (owner : Fin r)
    (howner : FirstOwned (Eligible (b + 3)) owner
      (relabelSubgroup q (physicalSubgroup H))) :
    ∃ (hn : w ≤ b + 3) (i : Non2TransitiveActionClass (Fin w)),
      relabelSubgroup q (physicalSubgroup H) ∈
        FusionWidthCanonicalFamily
          (non2FirstOwnerAction w (owner, i)) hn
          (non2FirstOwnerPredicate Eligible w (owner, i) (b + 3 - w)) := by
  letI : C.normal.Normal := C.normal_normal
  have hnon2 : ¬ IsPGroup 2
      (OrbitProfileFromOrbits.orbitImage
        (C3ComplementSource b H) C.orbit) :=
    strict_ternaryRelativeHead_not_isPGroup_two C.normal C.high
  obtain ⟨i, eO, himage⟩ := Non2TransitiveActionClass.orbit_cover
    (C3ComplementSource b H) C.orbit hw hnon2
  have hn : w ≤ b + 3 := by
    have hwb := width_le H C.orbit hw
    omega
  refine ⟨hn, i, ?_⟩
  exact C.mem_non2FirstOwnerCanonicalFamily_forAction Eligible hEligible H hw q
    hordinary owner howner i eO himage

/-- Existential-width wrapper used when no finite-width classification is
needed by the caller. -/
theorem Data.mem_non2FirstOwnerCanonicalFamily
    {r b : ℕ}
    (Eligible : ∀ n, Fin r → Subgroup (Equiv.Perm (Fin n)) → Prop)
    (hEligible : DegreeNaturalOwnerMenu Eligible)
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)))
    (C : Data H)
    (q : TernaryCyclic ⊕ Fin b ≃ Fin (b + 3))
    (hordinary : ¬ IsCriticalSubgroup (b + 3)
      (relabelSubgroup q (physicalSubgroup H)))
    (owner : Fin r)
    (howner : FirstOwned (Eligible (b + 3)) owner
      (relabelSubgroup q (physicalSubgroup H))) :
    ∃ (w : ℕ) (hn : w ≤ b + 3)
      (i : Non2TransitiveActionClass (Fin w)),
      relabelSubgroup q (physicalSubgroup H) ∈
        FusionWidthCanonicalFamily
          (non2FirstOwnerAction w (owner, i)) hn
          (non2FirstOwnerPredicate Eligible w (owner, i) (b + 3 - w)) := by
  let w := Nat.card C.orbit.orbit
  obtain ⟨hn, i, hmem⟩ := C.mem_non2FirstOwnerCanonicalFamily_atWidth
    Eligible hEligible H rfl q hordinary owner howner
  exact ⟨w, hn, i, hmem⟩

end C3HighNestedCarrier

/-- Once the four complete high-C3 branches are ordered by first ownership,
each branch lands in the matching owner/action cell of the general non-2
fusion menu.  This is the c=1 audit interface for branch-specific estimates. -/
theorem c3PhysicalStructuralBranch_firstOwner_mem_non2CanonicalFamily
    {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}
    (hordinary : ¬ IsCriticalSubgroup n G)
    (owner : Fin 4)
    (howner : FirstOwned (c3PhysicalStructuralBranchMenu n) owner G) :
    ∃ (w : ℕ) (hn : w ≤ n)
      (i : Non2TransitiveActionClass (Fin w)),
      G ∈ FusionWidthCanonicalFamily
        (non2FirstOwnerAction w (owner, i)) hn
        (non2FirstOwnerPredicate c3PhysicalStructuralBranchMenu
          w (owner, i) (n - w)) := by
  rcases howner.1 with ⟨b, e, H, hphysical, o, N, hN,
    hHigh, hEarlier, hk⟩
  have hdegree : b + 3 = n := by
    have hcard := Nat.card_congr e
    have hternary : Nat.card TernaryCyclic = 3 := by
      rw [Nat.card_congr RepeatedMarkerOwnerBound.ternaryFinEquiv,
        Nat.card_fin]
    rw [Nat.card_sum, hternary, Nat.card_fin, Nat.card_fin] at hcard
    omega
  subst n
  let C : C3HighNestedCarrier.Data H := ⟨o, N, hN, hHigh⟩
  have hordinary' : ¬ IsCriticalSubgroup (b + 3)
      (relabelSubgroup e (C3HighNestedCarrier.physicalSubgroup H)) := by
    rwa [hphysical]
  have howner' : FirstOwned (c3PhysicalStructuralBranchMenu (b + 3)) owner
      (relabelSubgroup e (C3HighNestedCarrier.physicalSubgroup H)) := by
    rwa [hphysical]
  simpa only [hphysical] using
    C.mem_non2FirstOwnerCanonicalFamily
      c3PhysicalStructuralBranchMenu
      c3PhysicalStructuralBranchMenu_natural H e hordinary' owner howner'

end SymmetricSubgroupAsymptotics

end
