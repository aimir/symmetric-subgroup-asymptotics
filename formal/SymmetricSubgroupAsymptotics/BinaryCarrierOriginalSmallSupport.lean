import SymmetricSubgroupAsymptotics.BinaryCarrierOriginalCyclicFourRankGap
import SymmetricSubgroupAsymptotics.BinaryMarkedInvariantsCongr
import SymmetricSubgroupAsymptotics.BinaryTerminalFullTailCount
import SymmetricSubgroupAsymptotics.BinaryPGroupSubgroupCount

/-! Small-support attachment for the thirteen literal noncritical colors.
The character and H² marks are measured on each original full tail. Only
the number of such tails is bounded by inverse images in the master
product. Repeated original colors, their points, and arbitrary predicates
on the complete original subgroup remain distinct throughout. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierOriginalSmallSupport

open BinaryCarrierWord BinaryCarrierOccurrenceWord
open BinaryCarrierOriginalCyclicFourHall

local instance subgroupFinite {G : Type*} [Group G] [Finite G] :
    Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

attribute [local instance] Fintype.ofFinite

def halfSupport (a : ℕ) (m : CarrierTarget → ℕ) : ℕ :=
  2*a + 4*BinaryCarrierOriginalActions.scale m

def sourceOrder (a : ℕ) (m : CarrierTarget → ℕ) : ℕ :=
  2*a + carrierOrder m

abbrev Tail (a : ℕ) (m : CarrierTarget → ℕ) :=
  OrbitProfileProductGroup (multiplicity a m) action

abbrev TailPoints (a : ℕ) (m : CarrierTarget → ℕ) :=
  OrbitProfilePoints points (multiplicity a m)

abbrev FullTail (a : ℕ) (m : CarrierTarget → ℕ) :=
  {H : Subgroup (Tail a m) // OrbitProfileProductFull (multiplicity a m) action H}

abbrev SourceTail (a : ℕ) (m : CarrierTarget → ℕ) :=
  OccurrenceProduct sourceFactor (multiplicity a m)

/-- The source epimorphism keeps the original color and occurrence index. -/
def tailMap (a : ℕ) (m : CarrierTarget → ℕ) : SourceTail a m →* Tail a m where
  toFun f t j := hom t (f t j)
  map_one' := by funext t j; exact (hom t).map_one
  map_mul' f g := by funext t j; exact (hom t).map_mul (f t j) (g t j)

theorem tailMap_surjective (a : ℕ) (m : CarrierTarget → ℕ) :
    Function.Surjective (tailMap a m) := by
  intro f
  choose g hg using fun t j => hom_surjective t (f t j)
  exact ⟨g, funext fun t => funext fun j => hg t j⟩

def sourceTailChart (a : ℕ) (m : CarrierTarget → ℕ) :
    SourceTail a m ≃* (Multiplicative (Fin a → ZMod 4) × Carrier m) :=
  (splitOccurrences a m).trans
    ((cyclicFourCoordinates a).prodCongr (MulEquiv.refl (Carrier m)))

theorem tailPoints_card (a : ℕ) (m : CarrierTarget → ℕ) :
    Nat.card (TailPoints a m) = 2 * halfSupport a m := by
  rw [Nat.card_eq_fintype_card]
  simp only [TailPoints, OrbitProfilePoints, Fintype.card_sigma,
    Fintype.card_prod, Fintype.card_fin]
  rw [Fintype.sum_option]
  change a * Fintype.card (ZMod 4) +
    (∑ t, m t * Fintype.card (BinaryCarrierOriginalActions.points t)) = _
  simp only [ZMod.card, BinaryCarrierOriginalActions.point_card]
  unfold halfSupport BinaryCarrierOriginalActions.scale
  rw [Finset.mul_sum]
  have he : (∑ t, m t * (8 * BinaryCarrierOriginalActions.factorScaleNat t)) =
      2 * ∑ t, 4 * (m t * BinaryCarrierOriginalActions.factorScaleNat t) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [he]
  ring

theorem occurrence_of_halfSupport_pos (a : ℕ) (m : CarrierTarget → ℕ)
    (hC : 0 < halfSupport a m) : Nonempty (Σ t, Fin (multiplicity a m t)) := by
  by_contra h
  have hz (t : Target) : multiplicity a m t = 0 := by
    by_contra ht
    exact h ⟨⟨t, ⟨0, Nat.pos_of_ne_zero ht⟩⟩⟩
  have ha : a = 0 := hz none
  have hm (t : CarrierTarget) : m t = 0 := hz (some t)
  simp [halfSupport, ha, BinaryCarrierOriginalActions.scale, hm] at hC

variable (a : ℕ) (m : CarrierTarget → ℕ) {L : ℕ}
    (occurrences : Fin L ≃ (Σ t, Fin (m t)))

include occurrences in
theorem sourceTail_card : Nat.card (SourceTail a m) = 2 ^ sourceOrder a m := by
  rw [Nat.card_congr (sourceTailChart a m).toEquiv, Nat.card_prod,
    carrier_card m occurrences]
  have hc : Nat.card (Multiplicative (Fin a → ZMod 4)) = 4^a := by
    simp [Nat.card_eq_fintype_card]
  rw [hc, show (4 : ℕ) = 2^2 by decide, ← pow_mul, ← pow_add]
  rfl

include occurrences in
theorem sourceOrder_le_halfSupport : 4 * sourceOrder a m ≤ 7 * halfSupport a m := by
  have h := carrierOrder_le_scale m occurrences
  unfold sourceOrder halfSupport
  omega

include occurrences in
theorem tail_binary : IsPGroup 2 (Tail a m) :=
  (IsPGroup.of_card (sourceTail_card a m occurrences)).of_surjective
    (tailMap a m) (tailMap_surjective a m)

include occurrences in
/-- Only the number of original tails uses the master preimage. -/
theorem fullTail_card_le : Nat.card (FullTail a m) ≤ binarySubspaceCount (sourceOrder a m) :=
  BinaryPGroupSubgroupCount.onto_subfamily_card_le_binarySubspaceCount
    (tailMap a m) (tailMap_surjective a m) (sourceOrder a m)
    (sourceTail_card a m occurrences) (OrbitProfileProductFull (multiplicity a m) action)

include occurrences in
/-- Both marks belong to the same original tail on its faithful original
points, before the unrelated injection used to count the tail family. -/
theorem fullTail_marks (hC : 0 < halfSupport a m) (H : FullTail a m) :
    binaryCharacterRank H.1 + 1 ≤ halfSupport a m ∧
      Module.finrank (ZMod 2) (terminalRestrictedInflationKernel H.1) ≤ halfSupport a m := by
  let ρ := orbitProfileProductAction (multiplicity a m) action
  let H' := H.1.map ρ
  let e : H.1 ≃* H' := H.1.equivMapOfInjective ρ
    (orbitProfileProductAction_injective (multiplicity a m) action)
  have hH' : IsPGroup 2 H' := ((tail_binary a m occurrences).to_subgroup H.1).map ρ
  have hfull : OrbitProfileFullOn action (Equiv.refl (TailPoints a m)) H' :=
    (orbitProfileFullOn_iff action 1 H').mpr (orbitProfileProductFull_map H.2)
  let o := Classical.choice (occurrence_of_halfSupport_pos a m hC)
  have hm := original_noncritical_marks a m (Equiv.refl (TailPoints a m)) H' hH'
    hfull o.1 o.2
  change (binaryCharacterRank H' + 1 ≤ Nat.card (TailPoints a m) / 2) ∧
    (Module.finrank (ZMod 2) (terminalRestrictedInflationKernel H') ≤
      Nat.card (TailPoints a m) / 2) at hm
  rw [← binaryCharacterRank_congr e,
    ← terminalRestrictedInflationKernel_finrank_congr e] at hm
  have hc : Nat.card (TailPoints a m) / 2 = halfSupport a m := by
    rw [tailPoints_card]
    omega
  simpa only [hc] using hm

def actualFactor (t : Target) : Factor :=
  BinaryCarrierMixedProfile.localFactor points action
    (fun t => (sourceFactor t).binary.of_surjective (hom t) (hom_surjective t)) t

/-- Only the critical coordinates are regrouped; the original tail is fixed. -/
def criticalOnlyChart (p : CriticalProfile) :
    BinaryCarrierCriticalOccurrence.OriginalProduct p actualFactor (multiplicity a m) ≃*
      (CriticalProfileCoordinateGroup p × Tail a m) :=
  (criticalProfileProductEquiv p).prodCongr (MulEquiv.refl (Tail a m))

theorem criticalOnlyChart_tail (p : CriticalProfile)
    (K : Subgroup (BinaryCarrierCriticalOccurrence.OriginalProduct
      p actualFactor (multiplicity a m))) :
    SubdirectTailImage.tail (K.map (criticalOnlyChart a m p).toMonoidHom) =
      K.map (MonoidHom.snd _ _) := by
  unfold SubdirectTailImage.tail
  rw [Subgroup.map_map]
  rfl

theorem criticalOnlyChart_full (p : CriticalProfile)
    (K : Subgroup (BinaryCarrierCriticalOccurrence.OriginalProduct
      p actualFactor (multiplicity a m)))
    (hK : BinaryCarrierCriticalOccurrence.OriginalFull p actualFactor (multiplicity a m) K) :
    terminalCoordinatesFull p.abelianRank (criticalProfileNonabelianChoice p)
      (K.map (criticalOnlyChart a m p).toMonoidHom) := by
  have he : (K.map (criticalOnlyChart a m p).toMonoidHom).map (MonoidHom.fst _ _) =
      (K.map (MonoidHom.fst _ _)).map (criticalProfileProductEquiv p).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  have hc : CriticalProfileCoordinateFull p
      ((K.map (MonoidHom.fst _ _)).map (criticalProfileProductEquiv p).toMonoidHom) := by
    unfold CriticalProfileCoordinateFull
    rw [Subgroup.comap_map_eq_self_of_injective
      (f := (criticalProfileProductEquiv p).toMonoidHom)
      (criticalProfileProductEquiv p).injective]
    exact hK.1
  intro i
  have hi := criticalProfileCoordinateFull_nonabelian p _ hc i
  rw [← he, Subgroup.map_map] at hi
  exact hi

/-- Original predicates may be discarded only by this explicit inclusion.
The tail and every original critical coordinate remain the same groups. -/
def modelEmbeddingFullTail (p : CriticalProfile)
    (P : Subgroup (Equiv.Perm (ModelPoints p a m)) → Prop) :
    ModelFamily p a m P ↪ BinaryTerminalFullTailCount.Family
      p.abelianRank (criticalProfileNonabelianChoice p) (Tail a m)
      (OrbitProfileProductFull (multiplicity a m) action) (fun _ => True) :=
  (BinaryCarrierMixedProfile.modelEquivSplit points action
    (fun t => (sourceFactor t).binary.of_surjective (hom t) (hom_surjective t))
      p (multiplicity a m) P).toEmbedding.trans {
    toFun := fun K => ⟨K.1.map (criticalOnlyChart a m p).toMonoidHom, by
      rw [criticalOnlyChart_tail]
      exact K.2.1.2, criticalOnlyChart_full a m p K.1 K.2.1, True.intro⟩
    inj' := by
      intro K K' he
      apply Subtype.ext
      apply Subgroup.map_injective (f := (criticalOnlyChart a m p).toMonoidHom)
        (criticalOnlyChart a m p).injective
      exact congrArg Subtype.val he }

/-- Explicit fixed-profile model bound. The Gaussian factor keeps the
proved original rank gap; the subgroup count uses only the source order. -/
def bound (p : CriticalProfile) : ℝ :=
  (binarySubspaceCount (sourceOrder a m) : ℝ) *
    BinaryTerminalFullTailCount.prefactor p.rank (p.d8+p.e8) (halfSupport a m) *
      terminalGaussianWeight p.rank (halfSupport a m - 1)

include occurrences in
theorem modelFamily_card_le (p : CriticalProfile) (hC : 0 < halfSupport a m)
    (P : Subgroup (Equiv.Perm (ModelPoints p a m)) → Prop) :
    (Nat.card (ModelFamily p a m P) : ℝ) ≤ bound a m p := by
  have hfirst : (Nat.card (ModelFamily p a m P) : ℝ) ≤
      (Nat.card (BinaryTerminalFullTailCount.Family p.abelianRank
        (criticalProfileNonabelianChoice p) (Tail a m)
        (OrbitProfileProductFull (multiplicity a m) action) (fun _ => True)) : ℝ) := by
    exact_mod_cast Nat.card_le_card_of_injective (modelEmbeddingFullTail a m p P)
      (modelEmbeddingFullTail a m p P).injective
  have hmiddle := BinaryTerminalFullTailCount.card_le_uniform_weight
    p.abelianRank (criticalProfileNonabelianChoice p) (Tail a m)
    (OrbitProfileProductFull (multiplicity a m) action) (halfSupport a m)
    (fullTail_marks a m occurrences hC) (fun _ => True)
  simp only [criticalProfile_product_rank, CriticalProfileNonabelianIndex,
    Fintype.card_sum, Fintype.card_fin] at hmiddle
  apply (hfirst.trans hmiddle).trans
  unfold bound
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right
    · exact_mod_cast fullTail_card_le a m occurrences
    · exact BinaryTerminalFullTailCount.prefactor_nonneg _ _ _
  · have h := terminalGaussianWeight_term_le p.rank (halfSupport a m-1) 0
      (Nat.zero_le p.rank)
    have h1 : (1 : ℝ) ≤ terminalGaussianWeight p.rank (halfSupport a m-1) := by
      simpa using h
    linarith

include occurrences in
/-- Physical assembly uses the original thirteen-color denominator. No
normalizer of a source master replaces an original target normalizer. -/
theorem full_profile_card_le (p : CriticalProfile) (hC : 0 < halfSupport a m)
    {X : Type*} (labels : ModelPoints p a m ≃ X) :
    (Nat.card (FullOrbitProfileOn (BinaryCarrierMixedProfile.points points)
      (BinaryCarrierMixedProfile.multiplicity p (multiplicity a m))
      (BinaryCarrierMixedProfile.action points action) X) : ℝ) ≤
      ((2*p.rank + 4*a + 8*BinaryCarrierOriginalActions.scale m).factorial : ℝ) *
        bound a m p /
          BinaryCarrierMixedProfile.originalDenominator points action p (multiplicity a m) := by
  rw [← Nat.card_congr (assembledFullOrbitProfileEquiv
    (X := X) (m := BinaryCarrierMixedProfile.multiplicity p (multiplicity a m))
    (BinaryCarrierMixedProfile.action points action))]
  have hmodel :
      (Nat.card {K // OrbitProfileFull
        (m := BinaryCarrierMixedProfile.multiplicity p (multiplicity a m))
        (BinaryCarrierMixedProfile.action points action) 1 K} : ℝ) ≤ bound a m p := by
    simpa only [ModelFamily, BinaryCarrierMixedProfile.ModelFamily, and_true] using
      modelFamily_card_le a m occurrences p hC (fun _ => True)
  have h := assembledOrbitProfileOn_card_le_real_of_model_bound
    (orbitProfileFull_family_natural
      (BinaryCarrierMixedProfile.multiplicity p (multiplicity a m))
      (BinaryCarrierMixedProfile.action points action)) labels hmodel
  change _ ≤ ((BinaryCarrierMixedProfile.physicalDegree points p (multiplicity a m)).factorial : ℝ) *
    _ / BinaryCarrierMixedProfile.originalDenominator points action p (multiplicity a m) at h
  simpa only [physicalDegree_eq] using h

end SymmetricSubgroupAsymptotics.BinaryCarrierOriginalSmallSupport
