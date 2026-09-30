import SymmetricSubgroupAsymptotics.Non2PreE7ResidualPairPartition
import SymmetricSubgroupAsymptotics.Non2PreE7PhysicalFrontier

/-!
# The exact non-pair pre-E7 physical frontier

After the selected eight and residual four pair widths have been paid, the
chosen alphabet-violating orbit may be indexed by an action representative
which admits none of those pair frames.  This file proves that statement from
the literal physical nonmembership, rather than adding it as an action
classification premise.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

open RepeatedMarkerOwnerBound

/-- A pre-`E7` action with none of the four residual pair frames.  The eight
selected frames are already excluded by `PreE7ActionClass`. -/
def IsPreE7NonPairActionClass (w : ℕ) (i : PreE7ActionClass w) : Prop :=
  ∀ d : PreE7ResidualPairCountLabel, 2 * d.pairCount = w →
    ¬ Nonempty (BinaryPairFrame (preE7Action w i) (Fin d.pairCount))

abbrev PreE7NonPairActionClass (w : ℕ) :=
  {i : PreE7ActionClass w // IsPreE7NonPairActionClass w i}

instance preE7NonPairActionClassFintype (w : ℕ) :
    Fintype (PreE7NonPairActionClass w) :=
  Fintype.ofFinite _

def preE7NonPairAction (w : ℕ) (i : PreE7NonPairActionClass w) :
    Subgroup (Equiv.Perm (Fin w)) :=
  preE7Action w i.1

def preE7NonPairPredicate (w : ℕ)
    (i : PreE7NonPairActionClass w) (b : ℕ) :
    Subgroup (preE7NonPairAction w i × Equiv.Perm (Fin b)) → Prop :=
  preE7Predicate w i.1 b

theorem preE7NonPairPredicate_natural (w : ℕ)
    (i : PreE7NonPairActionClass w) (b : ℕ) :
    FusionOrbitNatural (preE7NonPairAction w i)
      (preE7NonPairPredicate w i b) :=
  preE7Predicate_natural w i.1 b

/-- Literal subgroup set underlying the exact non-pair residual subtype. -/
def PreE7NonPairResidualSubgroupSet (n : ℕ) :
    Set (Subgroup (Equiv.Perm (Fin n))) :=
  {H | H ∈ PreE7UnresolvedOutsideSubgroupSet n ∧
    H ∉ PreE7ResidualPairPhysical n}

def preE7NonPairResidualFamilyEquiv (n : ℕ) :
    PreE7NonPairResidualFamily n ≃ PreE7NonPairResidualSubgroupSet n where
  toFun H := ⟨H.1.1.1, ⟨H.1.1.2, H.1.2⟩, H.2⟩
  invFun H := ⟨⟨⟨H.1, H.2.1.1⟩, H.2.1.2⟩, H.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem preE7NonPairResidualRatio_eq_subgroupSet (n : ℕ) :
    preE7NonPairResidualRatio n =
      (Nat.card (PreE7NonPairResidualSubgroupSet n) : ℝ) /
        exactBenchmark n := by
  unfold preE7NonPairResidualRatio
  rw [Nat.card_congr (preE7NonPairResidualFamilyEquiv n)]

/-- A residual-width frame on a displayed pre-`E7` action places its whole
canonical family inside the already paid residual-pair physical union. -/
theorem mem_preE7ResidualPairPhysical_of_frame
    {n w : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (d : PreE7ResidualPairCountLabel) (a : PreE7ActionClass w)
    (hd : 2 * d.pairCount = w)
    (hframe : Nonempty
      (BinaryPairFrame (preE7Action w a) (Fin d.pairCount)))
    (hwn : w ≤ n)
    (hfamily : H ∈ FusionWidthCanonicalFamily (preE7Action w a) hwn
      (preE7Predicate w a (n - w))) :
    H ∈ PreE7ResidualPairPhysical n := by
  subst w
  let p : PreE7PairActionClass d.pairCount := ⟨a, hframe⟩
  let j : PreE7PairMenuIndex PreE7ResidualPairCountLabel.pairCount :=
    ⟨d, p⟩
  refine ⟨j, hwn, ?_⟩
  simpa only [j, p, preE7PairMenuHalfWidth, preE7PairMenuAction,
    preE7PairAction] using hfamily

/-- Transporting a residual pair frame back to the selected violating orbit
would place the original subgroup in the paid pair sector. -/
theorem isPreE7NonPairActionClass_of_violation
    {n w : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (hordinary : ¬ IsCriticalSubgroup n H)
    (hnonpair : H ∉ PreE7ResidualPairPhysical n)
    (o : OrbitProfileFromOrbits.Orbit H)
    (hbad : IsPreE7ViolationOrbit H o)
    (hw : Nat.card o.orbit = w) (hwn : w ≤ n)
    (i : Non2TransitiveActionClass (Fin w))
    (eO : Fin w ≃ o.orbit)
    (himage : relabelSubgroup eO i.representative =
      OrbitProfileFromOrbits.orbitImage H o) :
    IsPreE7NonPairActionClass w
      ⟨i, isPreE7ActionClass_of_violation H o hbad i eO himage⟩ := by
  let a : PreE7ActionClass w :=
    ⟨i, isPreE7ActionClass_of_violation H o hbad i eO himage⟩
  have hfamily : H ∈ FusionWidthCanonicalFamily (preE7Action w a) hwn
      (preE7Predicate w a (n - w)) := by
    simpa only [a, preE7Action, preE7Predicate] using
      (FusionOrbitProfileChart.mem_widthCanonicalFamily_non2Growing
        H hordinary o hw hwn i eO himage)
  intro d hd hframe
  exact hnonpair
    (mem_preE7ResidualPairPhysical_of_frame H d a hd hframe hwn hfamily)

/-- Every subgroup in the exact non-pair residual has a selected violating
orbit whose representative lies in the restricted non-pair action index. -/
theorem preE7NonPairResidual_physical_cover (n : ℕ)
    (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : H ∈ PreE7NonPairResidualSubgroupSet n) :
    ∃ j : GrowingQuotientPhysicalIndex
        (ι := fun w => PreE7NonPairActionClass w) 3 n,
      H ∈ GrowingQuotientCanonicalFamily 3 n preE7NonPairAction
        preE7NonPairPredicate j := by
  obtain ⟨o, hbinary, hmarker, hselected⟩ :=
    exists_preE7ViolationOrbit H hH.1.2
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
  have hfamily : H ∈ FusionWidthCanonicalFamily (preE7Action w a) hwn
      (preE7Predicate w a (n - w)) := by
    simpa only [a, preE7Action, preE7Predicate] using
      (FusionOrbitProfileChart.mem_widthCanonicalFamily_non2Growing
        H hH.1.1.1 o hw hwn i eO himage)
  have hfree : IsPreE7NonPairActionClass w a :=
    isPreE7NonPairActionClass_of_violation H hH.1.1.1 hH.2 o
      ⟨hbinary, hmarker, hselected⟩ hw hwn i eO himage
  let a' : PreE7NonPairActionClass w := ⟨a, hfree⟩
  have hmem : w ∈ Finset.Ico 3 (n + 1) :=
    Finset.mem_Ico.mpr ⟨hw3, Nat.lt_succ_of_le hwn⟩
  let j : GrowingQuotientPhysicalIndex
      (ι := fun d => PreE7NonPairActionClass d) 3 n :=
    ⟨⟨w, hmem⟩, a'⟩
  refine ⟨j, ?_⟩
  simpa only [j, a', preE7NonPairAction, preE7NonPairPredicate] using hfamily

/-- Fixed first-owner label paired with the genuinely non-pair pre-`E7`
action class. -/
abbrev PreE7NonPairFirstOwnerIndex (r w : ℕ) :=
  Fin r × PreE7NonPairActionClass w

def preE7NonPairFirstOwnerAction {r : ℕ} (w : ℕ)
    (j : PreE7NonPairFirstOwnerIndex r w) :
    Subgroup (Equiv.Perm (Fin w)) :=
  preE7NonPairAction w j.2

def preE7NonPairFirstOwnerPredicate {r : ℕ}
    (Eligible : ∀ n, Fin r → Subgroup (Equiv.Perm (Fin n)) → Prop)
    (w : ℕ) (j : PreE7NonPairFirstOwnerIndex r w) (b : ℕ) :
    Subgroup
      (preE7NonPairFirstOwnerAction w j × Equiv.Perm (Fin b)) → Prop :=
  ordinaryFirstOwnerLocalPredicate (preE7NonPairFirstOwnerAction w j)
    (Eligible (w + b)) j.1

theorem preE7NonPairFirstOwnerPredicate_natural {r : ℕ}
    (Eligible : ∀ n, Fin r → Subgroup (Equiv.Perm (Fin n)) → Prop)
    (hEligible : DegreeNaturalOwnerMenu Eligible)
    (w : ℕ) (j : PreE7NonPairFirstOwnerIndex r w) (b : ℕ) :
    FusionOrbitNatural (preE7NonPairFirstOwnerAction w j)
      (preE7NonPairFirstOwnerPredicate Eligible w j b) := by
  apply ordinaryFirstOwnerLocalPredicate_natural
  intro i s H
  exact hEligible rfl s i H

/-- Earlier owners plus the terminal residual branch cover the exact
non-pair pre-`E7` source. -/
theorem preE7NonPair_ownerOrResidual_physical_cover {r : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (hEarlier : DegreeNaturalOwnerMenu Earlier)
    (n : ℕ) (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : H ∈ PreE7NonPairResidualSubgroupSet n) :
    ∃ j : GrowingQuotientPhysicalIndex
        (ι := fun w => PreE7NonPairFirstOwnerIndex (r + 1) w) 3 n,
      H ∈ GrowingQuotientCanonicalFamily 3 n
        preE7NonPairFirstOwnerAction
        (preE7NonPairFirstOwnerPredicate
          (ownerOrResidualEligible Earlier)) j := by
  obtain ⟨o, hbad⟩ := exists_preE7ViolationOrbit H hH.1.2
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
    isPreE7NonPairActionClass_of_violation H hH.1.1.1 hH.2 o hbad
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
    preE7NonPairAction, preE7Action, preE7NonPairFirstOwnerPredicate,
    non2FirstOwnerAction, non2FirstOwnerPredicate] using
    (FusionOrbitProfileChart.mem_widthCanonicalFamily_non2FirstOwner
      (ownerOrResidualEligible Earlier)
      (ownerOrResidualEligible_natural Earlier hEarlier)
      H hH.1.1.1 owner howner o hw hwn i eO himage)

theorem preE7NonPair_ownerOrResidual_physicalBound_of_local {r : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (hEarlier : DegreeNaturalOwnerMenu Earlier)
    (D : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℕ → ℝ)
    (A : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ)
    (v : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℕ)
    (η δ c α : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ)
    (hlocal : GrowingQuotientLocalPhysicalBound 3
      preE7NonPairFirstOwnerAction
      (preE7NonPairFirstOwnerPredicate (ownerOrResidualEligible Earlier))
      D A v η δ c α) :
    GrowingQuotientPhysicalBound preE7NonPairResidualRatio 3
      D A v η δ c α := by
  apply growingQuotientPhysicalBound_of_local
    preE7NonPairResidualRatio 3 (by omega)
      PreE7NonPairResidualSubgroupSet preE7NonPairFirstOwnerAction
      (preE7NonPairFirstOwnerPredicate (ownerOrResidualEligible Earlier))
      D A v η δ c α
  · exact Filter.Eventually.of_forall (fun n => by
      rw [preE7NonPairResidualRatio_eq_subgroupSet n])
  · exact preE7NonPair_ownerOrResidual_physical_cover Earlier hEarlier
  · exact hlocal

/-- Complete owner-or-capacity constructor on the exact non-pair residual.
The axis sum and original action normalizer are retained verbatim. -/
noncomputable def
    preE7NonPair_exponentialForwardEstimate_of_ownerOrResidualAxes
    {r : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (hEarlier : DegreeNaturalOwnerMenu Earlier)
    {ρ : ℝ}
    (R : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → Type*)
    [∀ w i, Group (R w i)] [∀ w i, Finite (R w i)]
    (C : ∀ w (i : PreE7NonPairFirstOwnerIndex (r + 1) w) (_b : ℕ),
      {N : Subgroup (preE7NonPairFirstOwnerAction w i) // N.Normal} → ℝ)
    (A : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ)
    (v : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℕ)
    (η δ c α : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ)
    (ρR : ∀ w i, R w i →* Equiv.Perm (Fin (v w i)))
    (hρR : ∀ w i, Function.Injective (ρR w i))
    (hC : ∀ w i b N, 0 ≤ C w i b N)
    (hA : ∀ w i, A w i =
      (Nat.card (Subgroup.normalizer
        (preE7NonPairFirstOwnerAction w i :
          Set (Equiv.Perm (Fin w)))) : ℝ))
    (hα : ∀ w i, α w i = η w i + c w i)
    (haxis : ∀ w i b N (J : Subgroup (Equiv.Perm (Fin b))),
      fusionSurvivingEpiCount (preE7NonPairFirstOwnerAction w i)
          (preE7NonPairFirstOwnerPredicate
            (ownerOrResidualEligible Earlier) w i b) N J ≤
        (C w i b N * (2 : ℝ) ^ (η w i * b)) *
          completeQuotientWeight (R := R w i) J)
    (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8)
    (hp : GrowingQuotientParameterBound ρ v η δ c α)
    (hmass : GrowingMenuMassBound 3
      (fun w i b => fusionAxisEnvelopeTotal
        (preE7NonPairFirstOwnerAction w i) (C w i b)) A)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7NonPairResidualRatio := by
  let D : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℕ → ℝ :=
    fun w i b => fusionAxisEnvelopeTotal
      (preE7NonPairFirstOwnerAction w i) (C w i b)
  have hD : ∀ w i b, 0 ≤ D w i b := by
    intro w i b
    exact fusionAxisEnvelopeTotal_nonneg
      (preE7NonPairFirstOwnerAction w i) (C w i b) (hC w i b)
  have hP : ∀ w i b, FusionOrbitNatural
      (preE7NonPairFirstOwnerAction w i)
      (preE7NonPairFirstOwnerPredicate
        (ownerOrResidualEligible Earlier) w i b) := by
    intro w i b
    exact preE7NonPairFirstOwnerPredicate_natural
      (ownerOrResidualEligible Earlier)
      (ownerOrResidualEligible_natural Earlier hEarlier) w i b
  have henvelope : ∀ w i b (J : Subgroup (Equiv.Perm (Fin b))),
      fusionCompleteSourceSum (preE7NonPairFirstOwnerAction w i)
          (preE7NonPairFirstOwnerPredicate
            (ownerOrResidualEligible Earlier) w i b) J ≤
        (D w i b * (2 : ℝ) ^ (η w i * b)) *
          completeQuotientWeight (R := R w i) J := by
    intro w i b J
    exact fusionCompleteSourceSum_le_axisEnvelopeTotal_rpow
      (preE7NonPairFirstOwnerAction w i)
      (preE7NonPairFirstOwnerPredicate
        (ownerOrResidualEligible Earlier) w i b)
      (C w i b) (fun K => completeQuotientWeight (R := R w i) K)
      (η w i) (haxis w i b) J
  have hlocal : GrowingQuotientLocalPhysicalBound 3
      preE7NonPairFirstOwnerAction
      (preE7NonPairFirstOwnerPredicate (ownerOrResidualEligible Earlier))
      D A v η δ c α :=
    growingQuotientLocalPhysicalBound_of_completeSource 3
      preE7NonPairFirstOwnerAction
      (preE7NonPairFirstOwnerPredicate (ownerOrResidualEligible Earlier))
      R D A v η δ c α ρR hρR hP hD hA hα henvelope
  exact growingQuotient_exponentialForwardEstimate
    preE7NonPairResidualRatio 3 D A v η δ c α hρ hρ8 (by omega)
      hD
      (fun w i => by
        rw [hA w i]
        exact_mod_cast (Nat.card_pos (α :=
          Subgroup.normalizer
            (preE7NonPairFirstOwnerAction w i :
              Set (Equiv.Perm (Fin w))))))
      hp hmass hcoarse
      (preE7NonPair_ownerOrResidual_physicalBound_of_local
        Earlier hEarlier D A v η δ c α hlocal)

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
