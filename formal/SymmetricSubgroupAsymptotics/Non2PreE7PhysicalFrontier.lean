import SymmetricSubgroupAsymptotics.Non2UnipotentPrefixOutsidePartition
import SymmetricSubgroupAsymptotics.Non2GrowingPhysicalFrontier
import SymmetricSubgroupAsymptotics.Non2OwnerCapacityFrontier
import SymmetricSubgroupAsymptotics.FusionCompleteSourceEnvelope

/-!
# The exact pre-E7 physical frontier

Failure of the post-E7 orbit alphabet supplies one literal orbit whose image
is nonbinary, is not the natural three-point marker action, and admits no
selected unipotent-prefix pair frame.  This file retains that last exclusion
in the action index itself and covers the exact pre-E7 family by the resulting
restricted growing-action menu.

The final theorem is the numerical interface for the remaining outside
frontier: complete-source estimates are required only for these genuinely
pre-E7 action cells.  Selected UP actions are absent rather than paid again.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

open RepeatedMarkerOwnerBound

/-- One orbit witnessing failure of the post-E7 alphabet. -/
def IsPreE7ViolationOrbit {n : ℕ}
    (H : Subgroup (Equiv.Perm (Fin n)))
    (o : OrbitProfileFromOrbits.Orbit H) : Prop :=
  ¬ IsPGroup 2 (OrbitProfileFromOrbits.orbitImage H o) ∧
    ¬ (∃ e : Fin 3 ≃ o.orbit,
      relabelSubgroup e oddMarkerActionSubgroup =
        OrbitProfileFromOrbits.orbitImage H o) ∧
    ¬ SelectedUPPairOrbitAt H o

theorem exists_preE7ViolationOrbit {n : ℕ}
    (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : ¬ UPResidualOrbitCovered H) :
    ∃ o : OrbitProfileFromOrbits.Orbit H, IsPreE7ViolationOrbit H o := by
  unfold UPResidualOrbitCovered at hH
  push Not at hH
  simpa only [IsPreE7ViolationOrbit, not_exists] using hH

/-- A nonbinary action class retained by the pre-E7 frontier.  The negative
frame statement is invariant information about the chosen representative;
it introduces no frame choice and no extra counted pointing. -/
def IsPreE7ActionClass (w : ℕ)
    (i : Non2TransitiveActionClass (Fin w)) : Prop :=
  ∀ d : PairCountLabel, d.sourceDegree = w →
    ¬ Nonempty (BinaryPairFrame i.representative (Fin d.pairCount))

abbrev PreE7ActionClass (w : ℕ) :=
  {i : Non2TransitiveActionClass (Fin w) // IsPreE7ActionClass w i}

def preE7Action (w : ℕ) (i : PreE7ActionClass w) :
    Subgroup (Equiv.Perm (Fin w)) :=
  i.1.representative

def preE7Predicate (w : ℕ) (i : PreE7ActionClass w) (b : ℕ) :
    Subgroup (preE7Action w i × Equiv.Perm (Fin b)) → Prop :=
  non2GrowingPredicate w i.1 b

theorem preE7Predicate_natural (w : ℕ)
    (i : PreE7ActionClass w) (b : ℕ) :
    FusionOrbitNatural (preE7Action w i) (preE7Predicate w i b) :=
  non2GrowingPredicate_natural w i.1 b

theorem isPreE7ActionClass_of_violation {n w : ℕ}
    (H : Subgroup (Equiv.Perm (Fin n)))
    (o : OrbitProfileFromOrbits.Orbit H)
    (hbad : IsPreE7ViolationOrbit H o)
    (i : Non2TransitiveActionClass (Fin w))
    (eO : Fin w ≃ o.orbit)
    (himage : relabelSubgroup eO i.representative =
      OrbitProfileFromOrbits.orbitImage H o) :
    IsPreE7ActionClass w i := by
  intro d hd hframe
  apply hbad.2.2
  refine ⟨d, ?_, hbad.1, ?_⟩
  · calc
      Nat.card o.orbit = Nat.card (Fin w) := (Nat.card_congr eO).symm
      _ = w := Nat.card_fin w
      _ = d.sourceDegree := hd.symm
  · obtain ⟨F⟩ := hframe
    let F' : BinaryPairFrame
        (relabelSubgroup eO i.representative) (Fin d.pairCount) :=
      F.relabelPoints eO
    exact ⟨himage ▸ F'⟩

/-- The literal subgroup set underlying the nested pre-E7 subtype. -/
def PreE7UnresolvedOutsideSubgroupSet (n : ℕ) :
    Set (Subgroup (Equiv.Perm (Fin n))) :=
  {H | H ∈ OutsideFitsSubgroupSetAt n ∧ ¬ UPResidualOrbitCovered H}

def preE7UnresolvedOutsideFamilyEquiv (n : ℕ) :
    PreE7UnresolvedOutsideFamily n ≃
      PreE7UnresolvedOutsideSubgroupSet n where
  toFun H := ⟨H.1.1, H.1.2, H.2⟩
  invFun H := ⟨⟨H.1, H.2.1⟩, H.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem preE7UnresolvedOutsideRatio_eq_subgroupSet (n : ℕ) :
    preE7UnresolvedOutsideRatio n =
      (Nat.card (PreE7UnresolvedOutsideSubgroupSet n) : ℝ) /
        exactBenchmark n := by
  unfold preE7UnresolvedOutsideRatio
  rw [Nat.card_congr (preE7UnresolvedOutsideFamilyEquiv n)]

/-- Every pre-E7 subgroup enters a cell indexed by an actual alphabet-
violating orbit.  The complete original subgroup and complement are retained;
the chosen orbit is used only to produce the action label. -/
theorem preE7UnresolvedOutside_physical_cover (n : ℕ)
    (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : H ∈ PreE7UnresolvedOutsideSubgroupSet n) :
    ∃ j : GrowingQuotientPhysicalIndex
        (ι := fun w => PreE7ActionClass w) 3 n,
      H ∈ GrowingQuotientCanonicalFamily 3 n preE7Action
        preE7Predicate j := by
  obtain ⟨o, hbinary, hmarker, hselected⟩ :=
    exists_preE7ViolationOrbit H hH.2
  let w : ℕ := Nat.card o.orbit
  have hw : Nat.card o.orbit = w := rfl
  let outside : OutsideOrbit H := ⟨o, hbinary, hmarker⟩
  have hw3 : 3 ≤ w := by
    have h := outsideOrbit_card_gt_two H outside
    change 2 < Nat.card o.orbit at h
    omega
  have hwn : w ≤ n := by
    have hcard := Nat.card_le_card_of_injective
      (Subtype.val : o.orbit → Fin n) Subtype.val_injective
    simpa only [hw, Nat.card_fin] using hcard
  obtain ⟨i, eO, himage⟩ := Non2TransitiveActionClass.orbit_cover
    H o hw hbinary
  have hpre : IsPreE7ActionClass w i :=
    isPreE7ActionClass_of_violation H o
      ⟨hbinary, hmarker, hselected⟩ i eO himage
  let a : PreE7ActionClass w := ⟨i, hpre⟩
  have hmem : w ∈ Finset.Ico 3 (n + 1) :=
    Finset.mem_Ico.mpr ⟨hw3, Nat.lt_succ_of_le hwn⟩
  let j : GrowingQuotientPhysicalIndex
      (ι := fun d => PreE7ActionClass d) 3 n :=
    ⟨⟨w, hmem⟩, a⟩
  refine ⟨j, ?_⟩
  simpa only [j, a, preE7Action, preE7Predicate] using
    (FusionOrbitProfileChart.mem_widthCanonicalFamily_non2Growing
      H hH.1.1 o hw hwn i eO himage)

abbrev PreE7FirstOwnerIndex (r w : ℕ) :=
  Fin r × PreE7ActionClass w

def preE7FirstOwnerAction {r : ℕ} (w : ℕ)
    (j : PreE7FirstOwnerIndex r w) :
    Subgroup (Equiv.Perm (Fin w)) :=
  preE7Action w j.2

def preE7FirstOwnerPredicate {r : ℕ}
    (Eligible : ∀ n, Fin r → Subgroup (Equiv.Perm (Fin n)) → Prop)
    (w : ℕ) (j : PreE7FirstOwnerIndex r w) (b : ℕ) :
    Subgroup (preE7FirstOwnerAction w j × Equiv.Perm (Fin b)) → Prop :=
  ordinaryFirstOwnerLocalPredicate (preE7FirstOwnerAction w j)
    (Eligible (w+b)) j.1

theorem preE7FirstOwnerPredicate_natural {r : ℕ}
    (Eligible : ∀ n, Fin r → Subgroup (Equiv.Perm (Fin n)) → Prop)
    (hEligible : DegreeNaturalOwnerMenu Eligible)
    (w : ℕ) (j : PreE7FirstOwnerIndex r w) (b : ℕ) :
    FusionOrbitNatural (preE7FirstOwnerAction w j)
      (preE7FirstOwnerPredicate Eligible w j b) := by
  apply ordinaryFirstOwnerLocalPredicate_natural
  intro i s H
  exact hEligible rfl s i H

/-- Earlier owners plus the residual branch cover the exact restricted
pre-E7 source.  The owner and the alphabet-violating action form one index,
so the residual capacity theorem is imposed only after every earlier owner
has rejected the same complete physical subgroup. -/
theorem preE7Unresolved_ownerOrResidual_physical_cover {r : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (hEarlier : DegreeNaturalOwnerMenu Earlier)
    (n : ℕ) (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : H ∈ PreE7UnresolvedOutsideSubgroupSet n) :
    ∃ j : GrowingQuotientPhysicalIndex
        (ι := fun w => PreE7FirstOwnerIndex (r+1) w) 3 n,
      H ∈ GrowingQuotientCanonicalFamily 3 n
        preE7FirstOwnerAction
        (preE7FirstOwnerPredicate (ownerOrResidualEligible Earlier)) j := by
  obtain ⟨o, hbad⟩ := exists_preE7ViolationOrbit H hH.2
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
  obtain ⟨owner, howner⟩ := firstOwned_exists
    (ownerOrResidualEligible Earlier n) H
      (ownerOrResidualEligible_cover Earlier H)
  have hmem : w ∈ Finset.Ico 3 (n + 1) :=
    Finset.mem_Ico.mpr ⟨hw3, Nat.lt_succ_of_le hwn⟩
  let j : GrowingQuotientPhysicalIndex
      (ι := fun d => PreE7FirstOwnerIndex (r+1) d) 3 n :=
    ⟨⟨w, hmem⟩, (owner, a)⟩
  refine ⟨j, ?_⟩
  simpa only [j, a, preE7FirstOwnerAction, preE7Action,
    preE7FirstOwnerPredicate, non2FirstOwnerAction,
    non2FirstOwnerPredicate] using
    (FusionOrbitProfileChart.mem_widthCanonicalFamily_non2FirstOwner
      (ownerOrResidualEligible Earlier)
      (ownerOrResidualEligible_natural Earlier hEarlier)
      H hH.1.1 owner howner o hw hwn i eO himage)

theorem preE7Unresolved_ownerOrResidual_physicalBound_of_local {r : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (hEarlier : DegreeNaturalOwnerMenu Earlier)
    (D : ∀ w, PreE7FirstOwnerIndex (r+1) w → ℕ → ℝ)
    (A : ∀ w, PreE7FirstOwnerIndex (r+1) w → ℝ)
    (v : ∀ w, PreE7FirstOwnerIndex (r+1) w → ℕ)
    (η δ c α : ∀ w, PreE7FirstOwnerIndex (r+1) w → ℝ)
    (hlocal : GrowingQuotientLocalPhysicalBound 3 preE7FirstOwnerAction
      (preE7FirstOwnerPredicate (ownerOrResidualEligible Earlier))
      D A v η δ c α) :
    GrowingQuotientPhysicalBound preE7UnresolvedOutsideRatio 3
      D A v η δ c α := by
  apply growingQuotientPhysicalBound_of_local
    preE7UnresolvedOutsideRatio 3 (by omega)
      PreE7UnresolvedOutsideSubgroupSet preE7FirstOwnerAction
      (preE7FirstOwnerPredicate (ownerOrResidualEligible Earlier))
      D A v η δ c α
  · exact Filter.Eventually.of_forall (fun n => by
      rw [preE7UnresolvedOutsideRatio_eq_subgroupSet n])
  · exact preE7Unresolved_ownerOrResidual_physical_cover Earlier hEarlier
  · exact hlocal

/-- Local complete-source estimates on the restricted action menu assemble
to the exact pre-E7 normalized family. -/
theorem preE7UnresolvedOutside_physicalBound_of_local
    (D : ∀ w, PreE7ActionClass w → ℕ → ℝ)
    (A : ∀ w, PreE7ActionClass w → ℝ)
    (v : ∀ w, PreE7ActionClass w → ℕ)
    (η δ c α : ∀ w, PreE7ActionClass w → ℝ)
    (hlocal : GrowingQuotientLocalPhysicalBound 3 preE7Action
      preE7Predicate D A v η δ c α) :
    GrowingQuotientPhysicalBound preE7UnresolvedOutsideRatio 3
      D A v η δ c α := by
  apply growingQuotientPhysicalBound_of_local
    preE7UnresolvedOutsideRatio 3 (by omega)
      PreE7UnresolvedOutsideSubgroupSet preE7Action preE7Predicate
      D A v η δ c α
  · exact Filter.Eventually.of_forall (fun n => by
      rw [preE7UnresolvedOutsideRatio_eq_subgroupSet n])
  · exact preE7UnresolvedOutside_physical_cover
  · exact hlocal

/-- Complete numerical constructor for the missing pre-E7 estimate.  Its
menu contains exactly action classes outside the post-E7 alphabet, so this
estimate and the existing E7 estimate can be added without paying a selected
UP action twice. -/
noncomputable def preE7Unresolved_exponentialForwardEstimate_of_non2
    { ρ : ℝ }
    (D : ∀ w, PreE7ActionClass w → ℕ → ℝ)
    (A : ∀ w, PreE7ActionClass w → ℝ)
    (v : ∀ w, PreE7ActionClass w → ℕ)
    (η δ c α : ∀ w, PreE7ActionClass w → ℝ)
    (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8)
    (hD : ∀ w i b, 0 ≤ D w i b) (hA : ∀ w i, 0 < A w i)
    (hp : GrowingQuotientParameterBound ρ v η δ c α)
    (hmass : GrowingMenuMassBound 3 D A)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hlocal : GrowingQuotientLocalPhysicalBound 3 preE7Action
      preE7Predicate D A v η δ c α) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7UnresolvedOutsideRatio :=
  growingQuotient_exponentialForwardEstimate
    preE7UnresolvedOutsideRatio 3 D A v η δ c α hρ hρ8 (by omega)
      hD hA hp hmass hcoarse
      (preE7UnresolvedOutside_physicalBound_of_local
        D A v η δ c α hlocal)

/-- Restricted owner-or-capacity endgame for the exact pre-E7 source.
Earlier branches and the terminal unowned branch may use different literal
normal-axis coefficients.  Axis summation, the unchanged complete quotient
moment and the original action normalizer are then assembled once. -/
noncomputable def
    preE7Unresolved_exponentialForwardEstimate_of_ownerOrResidualAxes
    {r : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (hEarlier : DegreeNaturalOwnerMenu Earlier)
    { ρ : ℝ }
    (R : ∀ w, PreE7FirstOwnerIndex (r+1) w → Type*)
    [∀ w i, Group (R w i)] [∀ w i, Finite (R w i)]
    (C : ∀ w (i : PreE7FirstOwnerIndex (r+1) w) (_b : ℕ),
      {N : Subgroup (preE7FirstOwnerAction w i) // N.Normal} → ℝ)
    (A : ∀ w, PreE7FirstOwnerIndex (r+1) w → ℝ)
    (v : ∀ w, PreE7FirstOwnerIndex (r+1) w → ℕ)
    (η δ c α : ∀ w, PreE7FirstOwnerIndex (r+1) w → ℝ)
    (ρR : ∀ w i, R w i →* Equiv.Perm (Fin (v w i)))
    (hρR : ∀ w i, Function.Injective (ρR w i))
    (hC : ∀ w i b N, 0 ≤ C w i b N)
    (hA : ∀ w i, A w i =
      (Nat.card (Subgroup.normalizer
        (preE7FirstOwnerAction w i :
          Set (Equiv.Perm (Fin w)))) : ℝ))
    (hα : ∀ w i, α w i = η w i + c w i)
    (haxis : ∀ w i b N (J : Subgroup (Equiv.Perm (Fin b))),
      fusionSurvivingEpiCount (preE7FirstOwnerAction w i)
          (preE7FirstOwnerPredicate (ownerOrResidualEligible Earlier) w i b)
          N J ≤
        (C w i b N * (2 : ℝ) ^ (η w i * b)) *
          completeQuotientWeight (R := R w i) J)
    (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8)
    (hp : GrowingQuotientParameterBound ρ v η δ c α)
    (hmass : GrowingMenuMassBound 3
      (fun w i b => fusionAxisEnvelopeTotal
        (preE7FirstOwnerAction w i) (C w i b)) A)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7UnresolvedOutsideRatio := by
  let D : ∀ w, PreE7FirstOwnerIndex (r+1) w → ℕ → ℝ :=
    fun w i b => fusionAxisEnvelopeTotal
      (preE7FirstOwnerAction w i) (C w i b)
  have hD : ∀ w i b, 0 ≤ D w i b := by
    intro w i b
    exact fusionAxisEnvelopeTotal_nonneg
      (preE7FirstOwnerAction w i) (C w i b) (hC w i b)
  have hP : ∀ w i b, FusionOrbitNatural
      (preE7FirstOwnerAction w i)
      (preE7FirstOwnerPredicate (ownerOrResidualEligible Earlier) w i b) := by
    intro w i b
    exact preE7FirstOwnerPredicate_natural
      (ownerOrResidualEligible Earlier)
      (ownerOrResidualEligible_natural Earlier hEarlier) w i b
  have henvelope : ∀ w i b (J : Subgroup (Equiv.Perm (Fin b))),
      fusionCompleteSourceSum (preE7FirstOwnerAction w i)
          (preE7FirstOwnerPredicate
            (ownerOrResidualEligible Earlier) w i b) J ≤
        (D w i b * (2 : ℝ) ^ (η w i * b)) *
          completeQuotientWeight (R := R w i) J := by
    intro w i b J
    exact fusionCompleteSourceSum_le_axisEnvelopeTotal_rpow
      (preE7FirstOwnerAction w i)
      (preE7FirstOwnerPredicate
        (ownerOrResidualEligible Earlier) w i b)
      (C w i b) (fun K => completeQuotientWeight (R := R w i) K)
      (η w i) (haxis w i b) J
  have hlocal : GrowingQuotientLocalPhysicalBound 3
      preE7FirstOwnerAction
      (preE7FirstOwnerPredicate (ownerOrResidualEligible Earlier))
      D A v η δ c α :=
    growingQuotientLocalPhysicalBound_of_completeSource 3
      preE7FirstOwnerAction
      (preE7FirstOwnerPredicate (ownerOrResidualEligible Earlier))
      R D A v η δ c α ρR hρR hP hD hA hα henvelope
  exact growingQuotient_exponentialForwardEstimate
    preE7UnresolvedOutsideRatio 3 D A v η δ c α hρ hρ8 (by omega)
      hD
      (fun w i => by
        rw [hA w i]
        exact_mod_cast (Nat.card_pos (α :=
          Subgroup.normalizer
            (preE7FirstOwnerAction w i :
              Set (Equiv.Perm (Fin w))))))
      hp hmass hcoarse
      (preE7Unresolved_ownerOrResidual_physicalBound_of_local
        Earlier hEarlier D A v η δ c α hlocal)

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
