import SymmetricSubgroupAsymptotics.Non2OutsideFrontierAdapter
import SymmetricSubgroupAsymptotics.GrowingQuotientPhysicalAssembly

/-!
# Literal growing non-2 physical frontier

The single selected bad orbit partitions the ambient outside family without
pointing multiplicity.  On the growing side, its exact action class gives the
sigma index used by the growing quotient theorem.  The local predicate
reconstructs the complete ordinary subgroup in degree `w+b`; hence it retains
the whole complement and all correlations with the selected orbit.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical

namespace SymmetricSubgroupAsymptotics

def non2GrowingAction (w : ℕ)
    (i : Non2TransitiveActionClass (Fin w)) :
    Subgroup (Equiv.Perm (Fin w)) :=
  i.representative

/-- The complete ordinary-remainder condition, reconstructed from the
literal selected action and its entire complement. -/
def non2GrowingPredicate (w : ℕ)
    (i : Non2TransitiveActionClass (Fin w)) (b : ℕ)
    (L : Subgroup (non2GrowingAction w i × Equiv.Perm (Fin b))) : Prop :=
  ¬ IsCriticalSubgroup (w + b)
    (relabelSubgroup finSumFinEquiv
      (L.map (fusionOrbitAction (non2GrowingAction w i))))

theorem non2GrowingPredicate_natural (w : ℕ)
    (i : Non2TransitiveActionClass (Fin w)) (b : ℕ) :
    FusionOrbitNatural (non2GrowingAction w i)
      (non2GrowingPredicate w i b) := by
  exact fusionOrbitNatural_of_relabel_invariant
    (non2GrowingAction w i) finSumFinEquiv
      (fun H => ¬ IsCriticalSubgroup (w + b) H)
      (fun s H => ordinaryRemainder_relabel_iff (w + b) s H)

/-- An exact orbit chart enters the uniform `w+b` predicate.  This is the
cross-degree version of `mem_widthCanonicalFamily_ordinary`; the equality
`w + (n-w) = n` is handled only by an actual point equivalence. -/
theorem FusionOrbitProfileChart.mem_widthCanonicalFamily_non2Growing
    {n w : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : ¬ IsCriticalSubgroup n H)
    (o : OrbitProfileFromOrbits.Orbit H)
    (hw : Nat.card o.orbit = w) (hn : w ≤ n)
    (i : Non2TransitiveActionClass (Fin w))
    (eO : Fin w ≃ o.orbit)
    (himage : relabelSubgroup eO (non2GrowingAction w i) =
      OrbitProfileFromOrbits.orbitImage H o) :
    H ∈ FusionWidthCanonicalFamily (non2GrowingAction w i) hn
      (non2GrowingPredicate w i (n-w)) := by
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
    H o (non2GrowingAction w i) eO eC himage
  have hrec := fusionDeletedModel_recovers
    (non2GrowingAction w i) K hblock hprojection
  have hlocal : non2GrowingPredicate w i (n-w)
      (fusionDeletedModel (non2GrowingAction w i) K) := by
    unfold non2GrowingPredicate
    rw [hrec]
    let r : Fin w ⊕ Fin (n-w) ≃ Fin (w + (n-w)) := finSumFinEquiv
    let s : Fin (w + (n-w)) ≃ Fin n := r.symm.trans e
    have hs : relabelSubgroup s (relabelSubgroup r K) = H := by
      rw [relabelSubgroup_trans]
      have hrs : r.trans s = e := by
        apply Equiv.ext
        intro x
        change e (r.symm (r x)) = e x
        exact congrArg e (r.symm_apply_apply x)
      rw [hrs]
      dsimp only [K]
      rw [relabelSubgroup_trans, Equiv.symm_trans_self,
        relabelSubgroup_refl]
    apply (ordinaryRemainder_relabel_equiv_iff
      (show w + (n-w) = n by omega) s (relabelSubgroup r K)).mp
    rwa [hs]
  exact fusionWidthCanonicalFamily_of_chart
    (non2GrowingAction w i) hn H e hblock hprojection
      (non2GrowingPredicate w i (n-w)) hlocal

namespace RepeatedMarkerOwnerBound

abbrev SmallSelectedOutsideFamilyAt (n : ℕ) :=
  {H : OutsideFitsFamilyAt n // selectedOutsideWidthAt H ≤ 4}

abbrev GrowingSelectedOutsideFamilyAt (n : ℕ) :=
  {H : OutsideFitsFamilyAt n // ¬ selectedOutsideWidthAt H ≤ 4}

def selectedOutsideWidthPartitionEquivAt (n : ℕ) :
    OutsideFitsFamilyAt n ≃
      SmallSelectedOutsideFamilyAt n ⊕ GrowingSelectedOutsideFamilyAt n :=
  (Equiv.sumCompl (fun H : OutsideFitsFamilyAt n =>
    selectedOutsideWidthAt H ≤ 4)).symm

theorem selectedOutsideWidth_card_partitionAt (n : ℕ) :
    Nat.card (OutsideFitsFamilyAt n) =
      Nat.card (SmallSelectedOutsideFamilyAt n) +
        Nat.card (GrowingSelectedOutsideFamilyAt n) := by
  rw [Nat.card_congr (selectedOutsideWidthPartitionEquivAt n), Nat.card_sum]

/-- Literal ambient subgroup set of the growing selected-width sector. -/
def GrowingSelectedOutsideSubgroupSet (n : ℕ) :
    Set (Subgroup (Equiv.Perm (Fin n))) :=
  Set.range (fun H : GrowingSelectedOutsideFamilyAt n => H.1.1.1)

def SmallSelectedOutsideSubgroupSet (n : ℕ) :
    Set (Subgroup (Equiv.Perm (Fin n))) :=
  Set.range (fun H : SmallSelectedOutsideFamilyAt n => H.1.1.1)

theorem growingSelectedOutsideSubgroupSet_card (n : ℕ) :
    Nat.card (GrowingSelectedOutsideSubgroupSet n) =
      Nat.card (GrowingSelectedOutsideFamilyAt n) := by
  exact (Nat.card_congr (Equiv.ofInjective
    (fun H : GrowingSelectedOutsideFamilyAt n => H.1.1.1)
    (fun H K h => Subtype.ext (Subtype.ext (Subtype.ext h))))).symm

theorem smallSelectedOutsideSubgroupSet_card (n : ℕ) :
    Nat.card (SmallSelectedOutsideSubgroupSet n) =
      Nat.card (SmallSelectedOutsideFamilyAt n) := by
  exact (Nat.card_congr (Equiv.ofInjective
    (fun H : SmallSelectedOutsideFamilyAt n => H.1.1.1)
    (fun H K h => Subtype.ext (Subtype.ext (Subtype.ext h))))).symm

theorem outsideFitsSubgroupSetAt_card (n : ℕ) :
    Nat.card (OutsideFitsSubgroupSetAt n) =
      Nat.card (OutsideFitsFamilyAt n) := by
  rw [Nat.card_congr (outsideFitsSubgroupSetAtEquiv n).symm]

theorem outsideFitsSubgroupSetAt_card_partition (n : ℕ) :
    Nat.card (OutsideFitsSubgroupSetAt n) =
      Nat.card (SmallSelectedOutsideSubgroupSet n) +
        Nat.card (GrowingSelectedOutsideSubgroupSet n) := by
  rw [outsideFitsSubgroupSetAt_card,
    selectedOutsideWidth_card_partitionAt,
    smallSelectedOutsideSubgroupSet_card,
    growingSelectedOutsideSubgroupSet_card]

def smallSelectedOutsideRatio (n : ℕ) : ℝ :=
  (Nat.card (SmallSelectedOutsideSubgroupSet n) : ℝ) /
    exactBenchmark n

def growingSelectedOutsideRatio (n : ℕ) : ℝ :=
  (Nat.card (GrowingSelectedOutsideSubgroupSet n) : ℝ) /
    exactBenchmark n

private def outsideFitsSubgroupSetDegreeEquiv (n : ℕ) :
    OutsideFitsSubgroupSet (halfDegree n) (parity n) ≃
      OutsideFitsSubgroupSetAt n :=
  Equiv.cast (congrArg (fun d =>
      {H : Subgroup (Equiv.Perm (Fin d)) // H ∈ OutsideFitsSubgroupSetAt d})
    (MarkerDegreeForwardRow.degree_identity n))

/-- Exact normalized decomposition of the remaining outside frontier. -/
theorem outsideFrontierRatio_selectedWidth_partition (n : ℕ) :
    OrdinaryFrontierClosure.outsideFrontierRatio n =
      smallSelectedOutsideRatio n + growingSelectedOutsideRatio n := by
  rw [outsideFrontierRatio_eq_subgroupSet]
  have hcard :
      Nat.card (OutsideFitsSubgroupSet (halfDegree n) (parity n)) =
        Nat.card (OutsideFitsSubgroupSetAt n) :=
    Nat.card_congr (outsideFitsSubgroupSetDegreeEquiv n)
  rw [hcard, outsideFitsSubgroupSetAt_card_partition, Nat.cast_add]
  unfold smallSelectedOutsideRatio growingSelectedOutsideRatio
  rw [add_div]

/-- The arbitrary-degree literal outside ratio.  This is definitionally the
whole source to which the cutoff-three non-2 theorem is applied. -/
def outsideFitsAtRatio (n : ℕ) : ℝ :=
  (Nat.card (OutsideFitsSubgroupSetAt n) : ℝ) / exactBenchmark n

theorem outsideFrontierRatio_eq_outsideFitsAtRatio (n : ℕ) :
    OrdinaryFrontierClosure.outsideFrontierRatio n =
      outsideFitsAtRatio n := by
  rw [outsideFrontierRatio_eq_subgroupSet]
  have hcard :
      Nat.card (OutsideFitsSubgroupSet (halfDegree n) (parity n)) =
        Nat.card (OutsideFitsSubgroupSetAt n) :=
    Nat.card_congr (outsideFitsSubgroupSetDegreeEquiv n)
  rw [hcard]
  rfl

/-- Every growing outside subgroup enters the exact sigma index used by the
uniform quotient assembly.  The same selected orbit determines both its
sector and its action label. -/
theorem growingSelectedOutside_physical_cover (n : ℕ)
    (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : H ∈ GrowingSelectedOutsideSubgroupSet n) :
    ∃ j : GrowingQuotientPhysicalIndex
        (ι := fun w => Non2TransitiveActionClass (Fin w)) 5 n,
      H ∈ GrowingQuotientCanonicalFamily 5 n non2GrowingAction
        non2GrowingPredicate j := by
  obtain ⟨G, rfl⟩ := hH
  let o : OutsideOrbit G.1.1.1 := selectedOutsideOrbitAt G.1
  let w : ℕ := selectedOutsideWidthAt G.1
  have hw : Nat.card o.1.orbit = w := rfl
  have hwn : w ≤ n := by
    have hcard := Nat.card_le_card_of_injective
      (Subtype.val : o.1.orbit → Fin n) Subtype.val_injective
    simpa only [hw, Nat.card_fin] using hcard
  obtain ⟨i, eO, himage⟩ := Non2TransitiveActionClass.orbit_cover
    G.1.1.1 o.1 hw o.2.1
  have hmem : w ∈ Finset.Ico 5 (n + 1) :=
    Finset.mem_Ico.mpr ⟨by omega, Nat.lt_succ_of_le hwn⟩
  let j : GrowingQuotientPhysicalIndex
      (ι := fun d => Non2TransitiveActionClass (Fin d)) 5 n :=
    ⟨⟨w, hmem⟩, i⟩
  refine ⟨j, ?_⟩
  exact FusionOrbitProfileChart.mem_widthCanonicalFamily_non2Growing
    G.1.1.1 G.1.1.2 o.1 hw hwn i eO himage

/-- Every outside subgroup, including the degree-three `C₃` and both
degree-four audit directions, enters the uniform cutoff-three sigma menu. -/
theorem outsideFitsAt_physical_cover (n : ℕ)
    (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : H ∈ OutsideFitsSubgroupSetAt n) :
    ∃ j : GrowingQuotientPhysicalIndex
        (ι := fun w => Non2TransitiveActionClass (Fin w)) 3 n,
      H ∈ GrowingQuotientCanonicalFamily 3 n non2GrowingAction
        non2GrowingPredicate j := by
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
      (ι := fun d => Non2TransitiveActionClass (Fin d)) 3 n :=
    ⟨⟨w, hmem⟩, i⟩
  refine ⟨j, ?_⟩
  exact FusionOrbitProfileChart.mem_widthCanonicalFamily_non2Growing
    H hH.1 o.1 hw hwn i eO himage

/-- Once the complete-source local envelope has been proved for every
non-2 transitive action, the growing selected-width ratio satisfies exactly
the physical hypothesis consumed by the numerical forward theorem. -/
theorem growingSelectedOutside_physicalBound_of_local
    (D : ∀ w, Non2TransitiveActionClass (Fin w) → ℕ → ℝ)
    (A : ∀ w, Non2TransitiveActionClass (Fin w) → ℝ)
    (v : ∀ w, Non2TransitiveActionClass (Fin w) → ℕ)
    (η δ c α : ∀ w, Non2TransitiveActionClass (Fin w) → ℝ)
    (hlocal : GrowingQuotientLocalPhysicalBound 5 non2GrowingAction
      non2GrowingPredicate D A v η δ c α) :
    GrowingQuotientPhysicalBound growingSelectedOutsideRatio 5
      D A v η δ c α := by
  apply growingQuotientPhysicalBound_of_local
    growingSelectedOutsideRatio 5 (by omega)
      GrowingSelectedOutsideSubgroupSet non2GrowingAction
      non2GrowingPredicate D A v η δ c α
  · exact Filter.Eventually.of_forall (fun _ => le_rfl)
  · exact growingSelectedOutside_physical_cover
  · exact hlocal

/-- The reusable general non-2 theorem now consumes the complete remaining
outside frontier directly.  Its local premise includes the `C₃` case and is
therefore the promised first audit of every proposed capacity estimate. -/
theorem outsideFitsAt_physicalBound_of_local
    (D : ∀ w, Non2TransitiveActionClass (Fin w) → ℕ → ℝ)
    (A : ∀ w, Non2TransitiveActionClass (Fin w) → ℝ)
    (v : ∀ w, Non2TransitiveActionClass (Fin w) → ℕ)
    (η δ c α : ∀ w, Non2TransitiveActionClass (Fin w) → ℝ)
    (hlocal : GrowingQuotientLocalPhysicalBound 3 non2GrowingAction
      non2GrowingPredicate D A v η δ c α) :
    GrowingQuotientPhysicalBound outsideFitsAtRatio 3
      D A v η δ c α := by
  apply growingQuotientPhysicalBound_of_local
    outsideFitsAtRatio 3 (by omega)
      OutsideFitsSubgroupSetAt non2GrowingAction
      non2GrowingPredicate D A v η δ c α
  · exact Filter.Eventually.of_forall (fun _ => le_rfl)
  · exact outsideFitsAt_physical_cover
  · exact hlocal

end RepeatedMarkerOwnerBound
end SymmetricSubgroupAsymptotics

end
