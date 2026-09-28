import SymmetricSubgroupAsymptotics.Non2GrowingPhysicalFrontier
import SymmetricSubgroupAsymptotics.OrdinaryFirstOwnerFiniteMenu

/-!
# First-owner assembly for the general non-2 frontier

An exhaustive finite owner menu is imposed on the complete physical subgroup,
before choosing its non-2 orbit chart.  The first eligible owner and the one
selected bad orbit form a single sigma index.  Consequently earlier owners and
the final owner-free capacity branch can use different comparator certificates
without charging any original subgroup twice.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical

namespace SymmetricSubgroupAsymptotics

abbrev Non2FirstOwnerIndex (r w : ℕ) :=
  Fin r × Non2TransitiveActionClass (Fin w)

def non2FirstOwnerAction {r : ℕ} (w : ℕ)
    (j : Non2FirstOwnerIndex r w) :
    Subgroup (Equiv.Perm (Fin w)) :=
  j.2.representative

def non2FirstOwnerPredicate {r : ℕ}
    (Eligible : ∀ n, Fin r → Subgroup (Equiv.Perm (Fin n)) → Prop)
    (w : ℕ) (j : Non2FirstOwnerIndex r w) (b : ℕ) :
    Subgroup (non2FirstOwnerAction w j × Equiv.Perm (Fin b)) → Prop :=
  ordinaryFirstOwnerLocalPredicate (non2FirstOwnerAction w j)
    (Eligible (w+b)) j.1

theorem non2FirstOwnerPredicate_natural {r : ℕ}
    (Eligible : ∀ n, Fin r → Subgroup (Equiv.Perm (Fin n)) → Prop)
    (hEligible : ∀ n i (s : Equiv.Perm (Fin n)) H,
      Eligible n i (relabelSubgroup s H) ↔ Eligible n i H)
    (w : ℕ) (j : Non2FirstOwnerIndex r w) (b : ℕ) :
    FusionOrbitNatural (non2FirstOwnerAction w j)
      (non2FirstOwnerPredicate Eligible w j b) :=
  ordinaryFirstOwnerLocalPredicate_natural
    (non2FirstOwnerAction w j) (Eligible (w+b))
      (hEligible (w+b)) j.1

/-- Cross-degree invariance is the form needed when `w+(n-w)` is identified
with the original ambient degree only after the orbit has been selected. -/
def DegreeNaturalOwnerMenu {r : ℕ}
    (Eligible : ∀ n, Fin r → Subgroup (Equiv.Perm (Fin n)) → Prop) :
    Prop :=
  ∀ {m n} (_h : m = n) (e : Fin m ≃ Fin n) i H,
    Eligible n i (relabelSubgroup e H) ↔ Eligible m i H

theorem FusionOrbitProfileChart.mem_widthCanonicalFamily_non2FirstOwner
    {r n w : ℕ}
    (Eligible : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (hEligible : DegreeNaturalOwnerMenu Eligible)
    (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : ¬ IsCriticalSubgroup n H)
    (owner : Fin r) (howner : FirstOwned (Eligible n) owner H)
    (o : OrbitProfileFromOrbits.Orbit H)
    (hw : Nat.card o.orbit = w) (hn : w ≤ n)
    (i : Non2TransitiveActionClass (Fin w))
    (eO : Fin w ≃ o.orbit)
    (himage : relabelSubgroup eO i.representative =
      OrbitProfileFromOrbits.orbitImage H o) :
    H ∈ FusionWidthCanonicalFamily
      (non2FirstOwnerAction w (owner, i)) hn
      (non2FirstOwnerPredicate Eligible w (owner, i) (n-w)) := by
  have hsplit := PermutationCharacterRankSplit.card_split
    (FusionOrbitProfileChart.orbitSubaction H o)
  have hcomp : Nat.card
      ↑((FusionOrbitProfileChart.orbitSubaction H o)ᶜ) = n-w := by
    change Nat.card o.orbit + Nat.card
      ↑((FusionOrbitProfileChart.orbitSubaction H o)ᶜ) =
        Nat.card (Fin n) at hsplit
    rw [hw, Nat.card_fin] at hsplit
    omega
  let eC : Fin (n-w) ≃
      ↑((FusionOrbitProfileChart.orbitSubaction H o)ᶜ) :=
    (Finite.equivFinOfCardEq hcomp).symm
  let e := FusionOrbitProfileChart.chart H o eO eC
  let K : Subgroup (Equiv.Perm (Fin w ⊕ Fin (n-w))) :=
    relabelSubgroup e.symm H
  have hblock := FusionOrbitProfileChart.chart_preserves H o eO eC
  have hprojection := FusionOrbitProfileChart.chart_projection_eq
    H o i.representative eO eC himage
  have hrec := fusionDeletedModel_recovers i.representative K hblock hprojection
  have hlocal : non2FirstOwnerPredicate Eligible w (owner, i) (n-w)
      (fusionDeletedModel i.representative K) := by
    let r₀ : Fin w ⊕ Fin (n-w) ≃ Fin (w + (n-w)) := finSumFinEquiv
    let s : Fin (w + (n-w)) ≃ Fin n := r₀.symm.trans e
    let L : Subgroup (Equiv.Perm (Fin (w + (n-w)))) :=
      relabelSubgroup r₀ K
    have hs : relabelSubgroup s L = H := by
      dsimp only [L]
      rw [relabelSubgroup_trans]
      have hrs : r₀.trans s = e := by
        apply Equiv.ext
        intro x
        change e (r₀.symm (r₀ x)) = e x
        exact congrArg e (r₀.symm_apply_apply x)
      rw [hrs]
      dsimp only [K]
      rw [relabelSubgroup_trans, Equiv.symm_trans_self,
        relabelSubgroup_refl]
    have hordinary : ¬ IsCriticalSubgroup (w + (n-w)) L := by
      apply (ordinaryRemainder_relabel_equiv_iff
        (show w + (n-w) = n by omega) s L).mp
      rwa [hs]
    have hownerL : FirstOwned (Eligible (w + (n-w))) owner L := by
      have htransport := firstOwned_transport_iff
        (Eligible (w + (n-w))) (Eligible n) (relabelSubgroup s)
        (fun j M => (hEligible (show w + (n-w) = n by omega) s j M).symm)
        owner L
      apply htransport.mpr
      rwa [hs]
    have hphysical :
        relabelSubgroup (finSumFinEquiv : Fin w ⊕ Fin (n-w) ≃
          Fin (w + (n-w)))
          ((fusionDeletedModel i.representative K).map
            (fusionOrbitAction i.representative)) = L := by
      dsimp only [L, r₀]
      exact congrArg
        (relabelSubgroup (finSumFinEquiv : Fin w ⊕ Fin (n-w) ≃
          Fin (w + (n-w)))) hrec
    unfold non2FirstOwnerPredicate ordinaryFirstOwnerLocalPredicate
    simp only [non2FirstOwnerAction]
    constructor
    · unfold ordinaryRemainderFusionPredicate
      exact hphysical.symm ▸ hordinary
    · exact hphysical.symm ▸ hownerL
  exact fusionWidthCanonicalFamily_of_chart i.representative hn H e
    hblock hprojection
      (non2FirstOwnerPredicate Eligible w (owner, i) (n-w)) hlocal

namespace RepeatedMarkerOwnerBound

/-- Exhaustive first ownership and the selected bad orbit give a literal
cutoff-three cover with index `owner × action class`. -/
theorem outsideFitsAt_firstOwner_physical_cover {r : ℕ}
    (Eligible : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (hEligible : DegreeNaturalOwnerMenu Eligible)
    (hcover : ∀ n H, H ∈ OutsideFitsSubgroupSetAt n →
      ∃ i, Eligible n i H)
    (n : ℕ) (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : H ∈ OutsideFitsSubgroupSetAt n) :
    ∃ j : GrowingQuotientPhysicalIndex
        (ι := fun w => Non2FirstOwnerIndex r w) 3 n,
      H ∈ GrowingQuotientCanonicalFamily 3 n
        non2FirstOwnerAction (non2FirstOwnerPredicate Eligible) j := by
  obtain ⟨owner, howner⟩ := firstOwned_exists (Eligible n) H
    (hcover n H hH)
  let G : OutsideFitsFamilyAt n := ⟨⟨H, hH.1⟩, hH.2⟩
  let o : OutsideOrbit H := selectedOutsideOrbitAt G
  let w : ℕ := selectedOutsideWidthAt G
  have hw : Nat.card o.1.orbit = w := rfl
  have hw3 : 3 ≤ w := by
    have := selectedOutsideWidthAt_gt_two G
    omega
  have hwn : w ≤ n := by
    have hcard := Nat.card_le_card_of_injective
      (Subtype.val : o.1.orbit → Fin n) Subtype.val_injective
    simpa only [hw, Nat.card_fin] using hcard
  obtain ⟨i, eO, himage⟩ := Non2TransitiveActionClass.orbit_cover
    H o.1 hw o.2.1
  have hmem : w ∈ Finset.Ico 3 (n + 1) :=
    Finset.mem_Ico.mpr ⟨hw3, Nat.lt_succ_of_le hwn⟩
  let j : GrowingQuotientPhysicalIndex
      (ι := fun d => Non2FirstOwnerIndex r d) 3 n :=
    ⟨⟨w, hmem⟩, (owner, i)⟩
  refine ⟨j, ?_⟩
  exact FusionOrbitProfileChart.mem_widthCanonicalFamily_non2FirstOwner
    Eligible hEligible H hH.1 owner howner o.1 hw hwn i eO himage

theorem outsideFitsAt_firstOwner_physicalBound_of_local {r : ℕ}
    (Eligible : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (hEligible : DegreeNaturalOwnerMenu Eligible)
    (hcover : ∀ n H, H ∈ OutsideFitsSubgroupSetAt n →
      ∃ i, Eligible n i H)
    (D : ∀ w, Non2FirstOwnerIndex r w → ℕ → ℝ)
    (A : ∀ w, Non2FirstOwnerIndex r w → ℝ)
    (v : ∀ w, Non2FirstOwnerIndex r w → ℕ)
    (η δ c α : ∀ w, Non2FirstOwnerIndex r w → ℝ)
    (hlocal : GrowingQuotientLocalPhysicalBound 3 non2FirstOwnerAction
      (non2FirstOwnerPredicate Eligible) D A v η δ c α) :
    GrowingQuotientPhysicalBound outsideFitsAtRatio 3
      D A v η δ c α := by
  apply growingQuotientPhysicalBound_of_local
    outsideFitsAtRatio 3 (by omega) OutsideFitsSubgroupSetAt
      non2FirstOwnerAction (non2FirstOwnerPredicate Eligible)
      D A v η δ c α
  · exact Filter.Eventually.of_forall (fun _ => le_rfl)
  · exact outsideFitsAt_firstOwner_physical_cover Eligible hEligible hcover
  · exact hlocal

/-- The full non-2 frontier enters the numerical forward theorem after exact
first ownership.  Each earlier owner and the final residual owner may use its
own complete-source certificate, while the global weighted mass still sees
the original normalizer of every selected action. -/
noncomputable def
    outsideFrontier_exponentialForwardEstimate_of_non2FirstOwner
    {r : ℕ}
    (Eligible : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (hEligible : DegreeNaturalOwnerMenu Eligible)
    (hcover : ∀ n H, H ∈ OutsideFitsSubgroupSetAt n →
      ∃ i, Eligible n i H)
    { ρ : ℝ }
    (D : ∀ w, Non2FirstOwnerIndex r w → ℕ → ℝ)
    (A : ∀ w, Non2FirstOwnerIndex r w → ℝ)
    (v : ∀ w, Non2FirstOwnerIndex r w → ℕ)
    (η δ c α : ∀ w, Non2FirstOwnerIndex r w → ℝ)
    (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8)
    (hD : ∀ w i b, 0 ≤ D w i b) (hA : ∀ w i, 0 < A w i)
    (hp : GrowingQuotientParameterBound ρ v η δ c α)
    (hmass : GrowingMenuMassBound 3 D A)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hlocal : GrowingQuotientLocalPhysicalBound 3 non2FirstOwnerAction
      (non2FirstOwnerPredicate Eligible) D A v η δ c α) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      OrdinaryFrontierClosure.outsideFrontierRatio := by
  let E := growingQuotient_exponentialForwardEstimate
    outsideFitsAtRatio 3 D A v η δ c α hρ hρ8 (by omega)
      hD hA hp hmass hcoarse
      (outsideFitsAt_firstOwner_physicalBound_of_local
        Eligible hEligible hcover D A v η δ c α hlocal)
  exact OrdinaryFrontierClosure.ExponentialForwardEstimate.of_le E 0
    (fun n _ => (outsideFrontierRatio_eq_outsideFitsAtRatio n).le)

end RepeatedMarkerOwnerBound
end SymmetricSubgroupAsymptotics

end
