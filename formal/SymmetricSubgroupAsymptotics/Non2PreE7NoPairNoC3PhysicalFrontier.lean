import SymmetricSubgroupAsymptotics.Non2PreE7C3Partition
import SymmetricSubgroupAsymptotics.Non2PreE7NonPairPhysicalFrontier
import SymmetricSubgroupAsymptotics.FusionPhysicalFilters

/-!
# The exact no-pair/no-C3 pre-E7 physical frontier

The complete regular-`C3` family has already been paid.  This file retains
its literal complement through the selected-orbit chart, so the final action
consumers are asked to bound only sources outside both paid pair sectors and
the paid regular-`C3` sector.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

open RepeatedMarkerOwnerBound

/-- The complete regular-`C3` physical family is invariant under relabelling
of its entire ambient point set. -/
theorem c3CompleteOrdinaryPhysicalSet_relabel_iff (b : ℕ)
    (s : Equiv.Perm (Fin (3 + b)))
    (H : Subgroup (Equiv.Perm (Fin (3 + b)))) :
    relabelSubgroup s H ∈ C3CompleteOrdinaryPhysicalSet b ↔
      H ∈ C3CompleteOrdinaryPhysicalSet b := by
  unfold C3CompleteOrdinaryPhysicalSet FusionRelabelledFamily
  constructor
  · rintro ⟨⟨K, hK⟩, h⟩
    let t : Equiv.Perm (TernaryCyclic ⊕ Fin b) :=
      (c3ResidualPointEquiv b).trans
        (s.symm.trans (c3ResidualPointEquiv b).symm)
    have ht : t.trans (c3ResidualPointEquiv b) =
        (c3ResidualPointEquiv b).trans s.symm := by
      ext x
      simp [t]
    have hK' : relabelSubgroup t K ∈
        FusionOrbitFamily ternaryRegularAction
          (FusionAcceptedOrbitPredicate ternaryRegularAction
            (C3CompleteOrdinaryPredicate b)) := by
      exact fusionLabelledFamily_relabel _ t hK
    refine ⟨⟨relabelSubgroup t K, hK'⟩, ?_⟩
    change relabelSubgroup (c3ResidualPointEquiv b)
      (relabelSubgroup t K) = H
    rw [relabelSubgroup_trans, ht]
    have hs := congrArg (relabelSubgroup s.symm) h
    simpa only [relabelSubgroup_trans, Equiv.self_trans_symm,
      relabelSubgroup_refl] using hs
  · rintro ⟨⟨K, hK⟩, rfl⟩
    let t : Equiv.Perm (TernaryCyclic ⊕ Fin b) :=
      (c3ResidualPointEquiv b).trans
        (s.trans (c3ResidualPointEquiv b).symm)
    have ht : t.trans (c3ResidualPointEquiv b) =
        (c3ResidualPointEquiv b).trans s := by
      ext x
      simp [t]
    have hK' : relabelSubgroup t K ∈
        FusionOrbitFamily ternaryRegularAction
          (FusionAcceptedOrbitPredicate ternaryRegularAction
            (C3CompleteOrdinaryPredicate b)) := by
      exact fusionLabelledFamily_relabel _ t hK
    refine ⟨⟨relabelSubgroup t K, hK'⟩, ?_⟩
    change relabelSubgroup (c3ResidualPointEquiv b)
      (relabelSubgroup t K) =
        relabelSubgroup s (relabelSubgroup (c3ResidualPointEquiv b) K)
    rw [relabelSubgroup_trans, ht, relabelSubgroup_trans]

/-- The transported complete regular-`C3` family is likewise invariant on
every ambient `Fin n`. -/
theorem c3CompleteOrdinaryPhysicalAt_relabel_iff (n : ℕ)
    (s : Equiv.Perm (Fin n)) (H : Subgroup (Equiv.Perm (Fin n))) :
    relabelSubgroup s H ∈ C3CompleteOrdinaryPhysicalAt n ↔
      H ∈ C3CompleteOrdinaryPhysicalAt n := by
  by_cases hn : 3 ≤ n
  · simp only [C3CompleteOrdinaryPhysicalAt, dif_pos hn, Set.mem_setOf_eq]
    let t : Equiv.Perm (Fin (3 + (n - 3))) :=
      (c3AmbientPointEquiv n hn).trans
        (s.trans (c3AmbientPointEquiv n hn).symm)
    have ht : (c3AmbientPointEquiv n hn).symm.trans t =
        s.trans (c3AmbientPointEquiv n hn).symm := by
      ext x
      simp [t]
    simpa only [relabelSubgroup_trans, ht] using
      c3CompleteOrdinaryPhysicalSet_relabel_iff (n - 3) t
        (relabelSubgroup (c3AmbientPointEquiv n hn).symm H)
  · simp [C3CompleteOrdinaryPhysicalAt, hn]

/-- Cross-degree form of the same invariance, used after the chosen orbit
and its complement have been put on `Fin (w + b)`. -/
theorem c3CompleteOrdinaryPhysicalAt_degree_relabel_iff
    {m n : ℕ} (hmn : m = n) (e : Fin m ≃ Fin n)
    (H : Subgroup (Equiv.Perm (Fin m))) :
    relabelSubgroup e H ∈ C3CompleteOrdinaryPhysicalAt n ↔
      H ∈ C3CompleteOrdinaryPhysicalAt m := by
  subst n
  exact c3CompleteOrdinaryPhysicalAt_relabel_iff m e H

/-- Pull the already paid regular-`C3` complement back to one complete local
orbit chart.  This is a predicate of the whole source, not of its action
projection alone. -/
def noC3CompleteSourcePredicate {w b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (H : Subgroup (U × Equiv.Perm (Fin b))) : Prop :=
  relabelSubgroup (finSumFinEquiv : Fin w ⊕ Fin b ≃ Fin (w + b))
      (H.map (fusionOrbitAction (Z := Fin b) U)) ∉
    C3CompleteOrdinaryPhysicalAt (w + b)

theorem noC3CompleteSourcePredicate_natural {w b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) :
    FusionOrbitNatural U (noC3CompleteSourcePredicate (b := b) U) := by
  exact fusionOrbitNatural_of_relabel_invariant U
    (finSumFinEquiv : Fin w ⊕ Fin b ≃ Fin (w + b))
    (fun H => H ∉ C3CompleteOrdinaryPhysicalAt (w + b))
    (fun s H => not_congr
      (c3CompleteOrdinaryPhysicalAt_relabel_iff (w + b) s H))

/-- The fixed first-owner predicate with the complete regular-`C3` source
removed on the same physical labels. -/
def preE7NoPairNoC3FirstOwnerPredicate {r : ℕ}
    (Eligible : ∀ n, Fin r → Subgroup (Equiv.Perm (Fin n)) → Prop)
    (w : ℕ) (j : PreE7NonPairFirstOwnerIndex r w) (b : ℕ) :
    Subgroup
      (preE7NonPairFirstOwnerAction w j × Equiv.Perm (Fin b)) → Prop :=
  fun H => preE7NonPairFirstOwnerPredicate Eligible w j b H ∧
    noC3CompleteSourcePredicate (preE7NonPairFirstOwnerAction w j) H

theorem preE7NoPairNoC3FirstOwnerPredicate_natural {r : ℕ}
    (Eligible : ∀ n, Fin r → Subgroup (Equiv.Perm (Fin n)) → Prop)
    (hEligible : DegreeNaturalOwnerMenu Eligible)
    (w : ℕ) (j : PreE7NonPairFirstOwnerIndex r w) (b : ℕ) :
    FusionOrbitNatural (preE7NonPairFirstOwnerAction w j)
      (preE7NoPairNoC3FirstOwnerPredicate Eligible w j b) :=
  fusionOrbitNatural_and (preE7NonPairFirstOwnerAction w j)
    (preE7NonPairFirstOwnerPredicate Eligible w j b)
    (noC3CompleteSourcePredicate (preE7NonPairFirstOwnerAction w j))
    (preE7NonPairFirstOwnerPredicate_natural Eligible hEligible w j b)
    (noC3CompleteSourcePredicate_natural
      (preE7NonPairFirstOwnerAction w j))

/-- The selected violating orbit enters the narrowed first-owner cell while
the no-`C3` condition stays attached to the same complete physical source. -/
theorem mem_widthCanonicalFamily_preE7NoPairNoC3FirstOwner
    {r n w : ℕ}
    (Eligible : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (hEligible : DegreeNaturalOwnerMenu Eligible)
    (H : Subgroup (Equiv.Perm (Fin n)))
    (hordinary : ¬ IsCriticalSubgroup n H)
    (hnoC3 : H ∉ C3CompleteOrdinaryPhysicalAt n)
    (owner : Fin r) (howner : FirstOwned (Eligible n) owner H)
    (o : OrbitProfileFromOrbits.Orbit H)
    (hw : Nat.card o.orbit = w) (hwn : w ≤ n)
    (i : PreE7NonPairActionClass w)
    (eO : Fin w ≃ o.orbit)
    (himage : relabelSubgroup eO (preE7NonPairAction w i) =
      OrbitProfileFromOrbits.orbitImage H o) :
    H ∈ FusionWidthCanonicalFamily
      (preE7NonPairFirstOwnerAction w (owner, i)) hwn
      (preE7NoPairNoC3FirstOwnerPredicate Eligible w (owner, i) (n - w)) := by
  have hsplit := PermutationCharacterRankSplit.card_split
    (FusionOrbitProfileChart.orbitSubaction H o)
  have hcomp : Nat.card
      ↑((FusionOrbitProfileChart.orbitSubaction H o)ᶜ) = n - w := by
    change Nat.card o.orbit + Nat.card
      ↑((FusionOrbitProfileChart.orbitSubaction H o)ᶜ) =
        Nat.card (Fin n) at hsplit
    rw [hw, Nat.card_fin] at hsplit
    omega
  let eC : Fin (n - w) ≃
      ↑((FusionOrbitProfileChart.orbitSubaction H o)ᶜ) :=
    (Finite.equivFinOfCardEq hcomp).symm
  let e := FusionOrbitProfileChart.chart H o eO eC
  let K : Subgroup (Equiv.Perm (Fin w ⊕ Fin (n - w))) :=
    relabelSubgroup e.symm H
  have hblock := FusionOrbitProfileChart.chart_preserves H o eO eC
  have hprojection := FusionOrbitProfileChart.chart_projection_eq
    H o (preE7NonPairAction w i) eO eC himage
  have hrec := fusionDeletedModel_recovers
    (preE7NonPairAction w i) K hblock hprojection
  let r₀ : Fin w ⊕ Fin (n - w) ≃ Fin (w + (n - w)) := finSumFinEquiv
  let s : Fin (w + (n - w)) ≃ Fin n := r₀.symm.trans e
  let L : Subgroup (Equiv.Perm (Fin (w + (n - w)))) :=
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
  have hordinaryL : ¬ IsCriticalSubgroup (w + (n - w)) L := by
    apply (ordinaryRemainder_relabel_equiv_iff
      (show w + (n - w) = n by omega) s L).mp
    rwa [hs]
  have hownerL : FirstOwned (Eligible (w + (n - w))) owner L := by
    have htransport := firstOwned_transport_iff
      (Eligible (w + (n - w))) (Eligible n) (relabelSubgroup s)
      (fun j M =>
        (hEligible (show w + (n - w) = n by omega) s j M).symm)
      owner L
    apply htransport.mpr
    rwa [hs]
  have hnoC3L : L ∉ C3CompleteOrdinaryPhysicalAt (w + (n - w)) := by
    intro hL
    apply hnoC3
    rw [← hs]
    exact (c3CompleteOrdinaryPhysicalAt_degree_relabel_iff
      (show w + (n - w) = n by omega) s L).mpr hL
  have hphysical :
      relabelSubgroup (finSumFinEquiv : Fin w ⊕ Fin (n - w) ≃
        Fin (w + (n - w)))
        ((fusionDeletedModel (preE7NonPairAction w i) K).map
          (fusionOrbitAction (preE7NonPairAction w i))) = L := by
    dsimp only [L, r₀]
    exact congrArg
      (relabelSubgroup (finSumFinEquiv : Fin w ⊕ Fin (n - w) ≃
        Fin (w + (n - w)))) hrec
  have hlocal : preE7NoPairNoC3FirstOwnerPredicate Eligible w
      (owner, i) (n - w)
      (fusionDeletedModel (preE7NonPairAction w i) K) := by
    constructor
    · unfold preE7NonPairFirstOwnerPredicate
        ordinaryFirstOwnerLocalPredicate
      simp only [preE7NonPairFirstOwnerAction, preE7NonPairAction]
      constructor
      · unfold ordinaryRemainderFusionPredicate
        exact hphysical.symm ▸ hordinaryL
      · exact hphysical.symm ▸ hownerL
    · unfold noC3CompleteSourcePredicate
      exact hphysical.symm ▸ hnoC3L
  exact fusionWidthCanonicalFamily_of_chart
    (preE7NonPairAction w i) hwn H e hblock hprojection
      (preE7NoPairNoC3FirstOwnerPredicate Eligible w
        (owner, i) (n - w)) hlocal

/-- Literal subgroup set underlying the exact residual after both pair cuts
and the complete regular-`C3` cut. -/
def PreE7NoPairNoC3ResidualSubgroupSet (n : ℕ) :
    Set (Subgroup (Equiv.Perm (Fin n))) :=
  {H | H ∈ PreE7NonPairResidualSubgroupSet n ∧
    H ∉ C3CompleteOrdinaryPhysicalAt n}

def preE7NoPairNoC3ResidualFamilyEquiv (n : ℕ) :
    PreE7NoPairNoC3ResidualFamily n ≃
      PreE7NoPairNoC3ResidualSubgroupSet n where
  toFun H := ⟨H.1.1.1.1, ⟨⟨H.1.1.1.2, H.1.1.2⟩, H.1.2⟩, H.2⟩
  invFun H := ⟨⟨⟨⟨H.1, H.2.1.1.1⟩, H.2.1.1.2⟩, H.2.1.2⟩, H.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem preE7NoPairNoC3ResidualRatio_eq_subgroupSet (n : ℕ) :
    preE7NoPairNoC3ResidualRatio n =
      (Nat.card (PreE7NoPairNoC3ResidualSubgroupSet n) : ℝ) /
        exactBenchmark n := by
  unfold preE7NoPairNoC3ResidualRatio
  rw [Nat.card_congr (preE7NoPairNoC3ResidualFamilyEquiv n)]

/-- Earlier owners plus the terminal residual branch cover the exact source
after both paid pair sectors and the paid regular-`C3` sector are removed. -/
theorem preE7NoPairNoC3_ownerOrResidual_physical_cover {r : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (hEarlier : DegreeNaturalOwnerMenu Earlier)
    (n : ℕ) (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : H ∈ PreE7NoPairNoC3ResidualSubgroupSet n) :
    ∃ j : GrowingQuotientPhysicalIndex
        (ι := fun w => PreE7NonPairFirstOwnerIndex (r + 1) w) 3 n,
      H ∈ GrowingQuotientCanonicalFamily 3 n
        preE7NonPairFirstOwnerAction
        (preE7NoPairNoC3FirstOwnerPredicate
          (ownerOrResidualEligible Earlier)) j := by
  obtain ⟨o, hbad⟩ := exists_preE7ViolationOrbit H hH.1.1.2
  let w : ℕ := Nat.card o.orbit
  have hw : Nat.card o.orbit = w := rfl
  let outside : OutsideOrbit H := ⟨o, hbad.1, hbad.2.1⟩
  have hw3 : 3 ≤ w := by
    have h := outsideOrbit_card_gt_two H outside
    change 2 < Nat.card o.orbit at h
    omega
  have hwn : w ≤ n := by
    have hcard := Nat.card_le_card_of_injective
      (Subtype.val : o.orbit → Fin n) Subtype.val_injective
    simpa only [hw, Nat.card_fin] using hcard
  obtain ⟨i, eO, himage⟩ := Non2TransitiveActionClass.orbit_cover
    H o hw hbad.1
  have hpre : IsPreE7ActionClass w i :=
    isPreE7ActionClass_of_violation H o hbad i eO himage
  let a : PreE7ActionClass w := ⟨i, hpre⟩
  have hfree : IsPreE7NonPairActionClass w a :=
    isPreE7NonPairActionClass_of_violation H hH.1.1.1.1 hH.1.2 o hbad
      hw hwn i eO himage
  let a' : PreE7NonPairActionClass w := ⟨a, hfree⟩
  obtain ⟨owner, howner⟩ := firstOwned_exists
    (ownerOrResidualEligible Earlier n) H
      (ownerOrResidualEligible_cover Earlier H)
  have hmem : w ∈ Finset.Ico 3 (n + 1) :=
    Finset.mem_Ico.mpr ⟨hw3, Nat.lt_succ_of_le hwn⟩
  let j : GrowingQuotientPhysicalIndex
      (ι := fun d => PreE7NonPairFirstOwnerIndex (r + 1) d) 3 n :=
    ⟨⟨w, hmem⟩, (owner, a')⟩
  refine ⟨j, ?_⟩
  simpa only [j, a', a, preE7NonPairFirstOwnerAction,
    preE7NonPairAction, preE7Action] using
    (mem_widthCanonicalFamily_preE7NoPairNoC3FirstOwner
      (ownerOrResidualEligible Earlier)
      (ownerOrResidualEligible_natural Earlier hEarlier)
      H hH.1.1.1.1 hH.2 owner howner o hw hwn a' eO (by
        simpa only [a', a, preE7NonPairAction, preE7Action] using himage))

theorem preE7NoPairNoC3_ownerOrResidual_physicalBound_of_local {r : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (hEarlier : DegreeNaturalOwnerMenu Earlier)
    (D : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℕ → ℝ)
    (A : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ)
    (v : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℕ)
    (η δ c α : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ)
    (hlocal : GrowingQuotientLocalPhysicalBound 3
      preE7NonPairFirstOwnerAction
      (preE7NoPairNoC3FirstOwnerPredicate
        (ownerOrResidualEligible Earlier))
      D A v η δ c α) :
    GrowingQuotientPhysicalBound preE7NoPairNoC3ResidualRatio 3
      D A v η δ c α := by
  apply growingQuotientPhysicalBound_of_local
    preE7NoPairNoC3ResidualRatio 3 (by omega)
      PreE7NoPairNoC3ResidualSubgroupSet preE7NonPairFirstOwnerAction
      (preE7NoPairNoC3FirstOwnerPredicate
        (ownerOrResidualEligible Earlier))
      D A v η δ c α
  · exact Filter.Eventually.of_forall (fun n => by
      rw [preE7NoPairNoC3ResidualRatio_eq_subgroupSet n])
  · exact preE7NoPairNoC3_ownerOrResidual_physical_cover
      Earlier hEarlier
  · exact hlocal

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
