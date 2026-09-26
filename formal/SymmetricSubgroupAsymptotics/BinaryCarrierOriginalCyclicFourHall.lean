import SymmetricSubgroupAsymptotics.BinaryCarrierOriginalActions
import SymmetricSubgroupAsymptotics.BinaryCarrierMixedOrder
import SymmetricSubgroupAsymptotics.BinaryCriticalCyclicFourHall
import Mathlib.Algebra.Group.Equiv.TypeTags

/-! The original regular cyclic-four color is added to all twelve carrier
colors. Master inverse images preserve every original occurrence. A literal
product chart supplies the actual critical/C4 Hall theorem; physical
normalizers and factorials remain those of the original target actions.
The exact source order exponent is bounded by6T+#P, hence by7T.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierOriginalCyclicFourHall

open BinaryCarrierWord BinaryCarrierOccurrenceWord

local instance subgroupFinite {G : Type*} [Group G] [Finite G] :
    Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

attribute [local instance] Fintype.ofFinite

abbrev CarrierTarget := BinaryCarrierOriginalActions.Target

/-- The actual regular action on its four points. -/
def cyclicFourAction : Multiplicative (ZMod 4) →* Equiv.Perm (ZMod 4) where
  toFun a := {
    toFun := fun x => x + a.toAdd
    invFun := fun x => x - a.toAdd
    left_inv := by intro x; simp
    right_inv := by intro x; simp }
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp [add_comm, add_left_comm]

theorem cyclicFourAction_injective : Function.Injective cyclicFourAction := by
  intro a b h
  have h0 := Equiv.congr_fun h 0
  simpa [cyclicFourAction] using h0

abbrev CyclicFourOriginal := cyclicFourAction.range

def cyclicFourEquiv : Multiplicative (ZMod 4) ≃* CyclicFourOriginal :=
  MonoidHom.ofInjective cyclicFourAction_injective

def cyclicFourFactor : Factor where
  Carrier := CyclicFourOriginal
  group := inferInstance
  finite := inferInstance
  binary := IsPGroup.of_card (n := 2) (by
    rw [← Nat.card_congr cyclicFourEquiv.toEquiv]
    norm_num)

/-- None is the original C4 color; every carrier color remains distinct. -/
abbrev Target := Option CarrierTarget

def points : Target → Type
  | none => ZMod 4
  | some t => BinaryCarrierOriginalActions.points t

instance (t : Target) : Fintype (points t) := by
  cases t <;> dsimp [points] <;> infer_instance

instance (t : Target) : Nonempty (points t) := by
  cases t <;> dsimp [points] <;> infer_instance

def action : (t : Target) → Subgroup (Equiv.Perm (points t))
  | none => cyclicFourAction.range
  | some t => BinaryCarrierOriginalActions.action t

def sourceFactor : Target → Factor
  | none => cyclicFourFactor
  | some t => BinaryCarrierOriginalActions.sourceFactor t

def hom : (t : Target) → (sourceFactor t).Carrier →* action t
  | none => MonoidHom.id _
  | some t => BinaryCarrierOriginalActions.hom t

theorem hom_surjective (t : Target) : Function.Surjective (hom t) := by
  cases t with
  | none => exact Function.surjective_id
  | some t => exact BinaryCarrierOriginalActions.hom_surjective t

def multiplicity (a : ℕ) (m : CarrierTarget → ℕ) : Target → ℕ
  | none => a
  | some t => m t

/-- The master product retains each original carrier occurrence. -/
abbrev Carrier (m : CarrierTarget → ℕ) :=
  OccurrenceProduct BinaryCarrierOriginalActions.sourceFactor m

section CarrierOrder

variable (m : CarrierTarget → ℕ) {L : ℕ}
    (occurrences : Fin L ≃ (Σ t, Fin (m t)))

def carrierEquiv :
    Product (BinaryCarrierMixedMenuWord.word
      (BinaryCarrierOriginalActions.occurrenceKinds m occurrences)) ≃* Carrier m := by
  rw [BinaryCarrierOriginalActions.occurrenceWord_eq]
  exact occurrenceEquiv BinaryCarrierOriginalActions.sourceFactor m occurrences

include occurrences in
theorem carrier_binary : IsPGroup 2 (Carrier m) :=
  (product_binary _).of_equiv (carrierEquiv m occurrences)

def carrierOrder : ℕ := Nat.log 2 (Nat.card (Carrier m))

include occurrences in
theorem carrier_card : Nat.card (Carrier m) = 2 ^ carrierOrder m := by
  obtain ⟨u, hu⟩ := (carrier_binary m occurrences).exists_card_eq
  unfold carrierOrder
  rw [hu, Nat.log_pow (by decide : 1 < 2)]

theorem sourceWordScale :
    BinaryCarrierMixedActions.wordScale
      (BinaryCarrierOriginalActions.occurrenceKinds m occurrences) =
        BinaryCarrierOriginalActions.scale m := by
  have h := BinaryCarrierMixedActions.wordScale_cast
    (BinaryCarrierOriginalActions.occurrenceKinds m occurrences)
  rw [BinaryCarrierOriginalActions.totalScale_occurrenceKinds] at h
  exact_mod_cast h

/-- The extra exponent counts every P source occurrence, even when its
original target color differs from the other occurrences using P. -/
theorem carrierOrder_le_sharp :
    carrierOrder m ≤ 6 * BinaryCarrierOriginalActions.scale m +
      BinaryCarrierMixedActions.pCount
        (BinaryCarrierOriginalActions.occurrenceKinds m occurrences) := by
  have h := BinaryCarrierMixedActions.product_card_le_order
    (BinaryCarrierOriginalActions.occurrenceKinds m occurrences)
  rw [Nat.card_congr (carrierEquiv m occurrences).toEquiv,
    carrier_card m occurrences, sourceWordScale m occurrences] at h
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h

include occurrences in
theorem carrierOrder_le_scale : carrierOrder m ≤ 7 * BinaryCarrierOriginalActions.scale m := by
  have hp := BinaryCarrierMixedActions.pCount_le_wordScale
    (BinaryCarrierOriginalActions.occurrenceKinds m occurrences)
  rw [sourceWordScale m occurrences] at hp
  have h := carrierOrder_le_sharp m occurrences
  omega

end CarrierOrder

/-- Separate the existing C4 occurrence coordinates without reindexing any
carrier occurrence, and without grouping distinct original colors. -/
def splitOccurrences (a : ℕ) (m : CarrierTarget → ℕ) :
    OccurrenceProduct sourceFactor (multiplicity a m) ≃*
      ((Fin a → CyclicFourOriginal) × Carrier m) where
  toFun f := (f none, fun t => f (some t))
  invFun f := fun t => match t with
    | none => f.1
    | some t => f.2 t
  left_inv f := by funext t; cases t <;> rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def cyclicFourCoordinates (a : ℕ) :
    (Fin a → CyclicFourOriginal) ≃* Multiplicative (Fin a → ZMod 4) :=
  (MulEquiv.piCongrRight fun _ : Fin a => cyclicFourEquiv.symm).trans
    (MulEquiv.piMultiplicative (fun _ : Fin a => ZMod 4)).symm

/-- Only proved group charts are used; the whole original critical image
may remain proper, and the complete master carrier tuple is retained. -/
def hallChart (p : CriticalProfile) (a : ℕ) (m : CarrierTarget → ℕ) :
    BinaryCarrierCriticalOccurrence.OriginalProduct p sourceFactor (multiplicity a m) ≃*
      (CriticalProfileCoordinateGroup p ×
        (Multiplicative (Fin a → ZMod 4) × Carrier m)) :=
  (criticalProfileProductEquiv p).prodCongr
    ((splitOccurrences a m).trans
      ((cyclicFourCoordinates a).prodCongr (MulEquiv.refl (Carrier m))))

theorem hallChart_critical_full (p : CriticalProfile) (a : ℕ) (m : CarrierTarget → ℕ)
    (H : Subgroup (BinaryCarrierCriticalOccurrence.OriginalProduct
      p sourceFactor (multiplicity a m)))
    (hH : BinaryCarrierCriticalOccurrence.OriginalFull p sourceFactor (multiplicity a m) H) :
    terminalCoordinatesFull p.abelianRank (criticalProfileNonabelianChoice p)
      (H.map (hallChart p a m).toMonoidHom) := by
  have he : (H.map (hallChart p a m).toMonoidHom).map (MonoidHom.fst _ _) =
      (H.map (MonoidHom.fst _ _)).map (criticalProfileProductEquiv p).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  have hc : CriticalProfileCoordinateFull p
      ((H.map (MonoidHom.fst _ _)).map (criticalProfileProductEquiv p).toMonoidHom) := by
    unfold CriticalProfileCoordinateFull
    rw [Subgroup.comap_map_eq_self_of_injective (criticalProfileProductEquiv p).injective]
    exact hH.1
  intro i
  have hi := criticalProfileCoordinateFull_nonabelian p _ hc i
  rw [← he, Subgroup.map_map] at hi
  exact hi

variable (p : CriticalProfile) (a : ℕ) (m : CarrierTarget → ℕ)

abbrev ModelPoints := BinaryCarrierMixedProfile.ModelPoints points p (multiplicity a m)

abbrev ModelFamily (P : Subgroup (Equiv.Perm (ModelPoints p a m)) → Prop) :=
  BinaryCarrierMixedProfile.ModelFamily points action p (multiplicity a m) P

/-- The exact generic master inverse image precedes the faithful chart.
Only its additional original conditions are then dropped by inclusion. -/
def modelEmbeddingHall
    (P : Subgroup (Equiv.Perm (ModelPoints p a m)) → Prop) :
    ModelFamily p a m P ↪ BinaryCriticalCyclicFourHall.ActualFamily
      p.abelianRank (criticalProfileNonabelianChoice p)
      (Multiplicative (Fin a → ZMod 4) × Carrier m) (fun _ => True) :=
  (BinaryCarrierMixedProfileEpimorphism.modelEmbeddingSourceFull
    points action sourceFactor hom hom_surjective p (multiplicity a m) P).trans {
      toFun := fun H => ⟨H.1.map (hallChart p a m).toMonoidHom,
        hallChart_critical_full p a m H.1 H.2.1, True.intro⟩
      inj' := by
        intro H K h
        apply Subtype.ext
        apply Subgroup.map_injective (f := (hallChart p a m).toMonoidHom)
          (hallChart p a m).injective
        exact congrArg
          (fun J : BinaryCriticalCyclicFourHall.ActualFamily
            p.abelianRank (criticalProfileNonabelianChoice p)
            (Multiplicative (Fin a → ZMod 4) × Carrier m) (fun _ => True) => J.1) h }

variable {L : ℕ} (occurrences : Fin L ≃ (Σ t, Fin (m t)))

include occurrences in
/-- Both original marks and the Hall count are supplied by the actual
groups. The exact carrier exponent also satisfies the proved cap7T. -/
theorem modelFamily_card_le_hall
    (P : Subgroup (Equiv.Perm (ModelPoints p a m)) → Prop) :
    (Nat.card (ModelFamily p a m P) : ℝ) ≤
      BinaryCriticalCyclicFourHall.bound p.rank (p.d8+p.e8) a (carrierOrder m) := by
  have h : (Nat.card (ModelFamily p a m P) : ℝ) ≤
      (Nat.card (BinaryCriticalCyclicFourHall.ActualFamily p.abelianRank
        (criticalProfileNonabelianChoice p)
        (Multiplicative (Fin a → ZMod 4) × Carrier m) (fun _ => True)) : ℝ) := by
    exact_mod_cast Nat.card_le_card_of_injective (modelEmbeddingHall p a m P)
      (modelEmbeddingHall p a m P).injective
  apply h.trans
  simpa only [criticalProfile_product_rank, CriticalProfileNonabelianIndex,
    Fintype.card_sum, Fintype.card_fin] using
    BinaryCriticalCyclicFourHall.actualFamily_card_le p.abelianRank
      (criticalProfileNonabelianChoice p) a (Carrier m) (carrierOrder m)
      (carrier_card m occurrences) (fun _ => True)

theorem physicalDegree_eq :
    BinaryCarrierMixedProfile.physicalDegree points p (multiplicity a m) =
      2*p.rank + 4*a + 8*BinaryCarrierOriginalActions.scale m := by
  unfold BinaryCarrierMixedProfile.physicalDegree
  rw [Fintype.sum_sum_type]
  change (∑ i, p.multiplicity i * Fintype.card (criticalActionPoints i)) +
      (∑ t, multiplicity a m t * Fintype.card (points t)) = _
  rw [p.physical_degree, Fintype.sum_option]
  change 2*p.rank + (a*Fintype.card (ZMod 4) +
    ∑ t, m t * Fintype.card (BinaryCarrierOriginalActions.points t)) = _
  simp only [ZMod.card, BinaryCarrierOriginalActions.point_card]
  rw [BinaryCarrierOriginalActions.scale, Finset.mul_sum]
  have he : (∑ t, m t * (8 * BinaryCarrierOriginalActions.factorScaleNat t)) =
      ∑ t, 8 * (m t * BinaryCarrierOriginalActions.factorScaleNat t) := by
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [he]
  ring

include occurrences in
/-- The original regular-C4 and twelve carrier normalizers and factorials
remain in the actual physical denominator, with no master substitutions. -/
theorem full_profile_card_le_hall {X : Type*}
    (labels : ModelPoints p a m ≃ X) :
    (Nat.card (FullOrbitProfileOn (BinaryCarrierMixedProfile.points points)
      (BinaryCarrierMixedProfile.multiplicity p (multiplicity a m))
      (BinaryCarrierMixedProfile.action points action) X) : ℝ) ≤
      ((2*p.rank + 4*a + 8*BinaryCarrierOriginalActions.scale m).factorial : ℝ) *
        BinaryCriticalCyclicFourHall.bound p.rank (p.d8+p.e8) a (carrierOrder m) /
          BinaryCarrierMixedProfile.originalDenominator points action p (multiplicity a m) := by
  rw [← Nat.card_congr (assembledFullOrbitProfileEquiv
    (X := X) (m := BinaryCarrierMixedProfile.multiplicity p (multiplicity a m))
    (BinaryCarrierMixedProfile.action points action))]
  have hmodel :
      (Nat.card {K // OrbitProfileFull
        (m := BinaryCarrierMixedProfile.multiplicity p (multiplicity a m))
        (BinaryCarrierMixedProfile.action points action) 1 K} : ℝ) ≤
      BinaryCriticalCyclicFourHall.bound p.rank (p.d8+p.e8) a (carrierOrder m) := by
    simpa only [ModelFamily, BinaryCarrierMixedProfile.ModelFamily, and_true] using
      modelFamily_card_le_hall p a m occurrences (fun _ => True)
  have h := assembledOrbitProfileOn_card_le_real_of_model_bound
    (orbitProfileFull_family_natural
      (BinaryCarrierMixedProfile.multiplicity p (multiplicity a m))
      (BinaryCarrierMixedProfile.action points action)) labels hmodel
  change _ ≤ ((BinaryCarrierMixedProfile.physicalDegree points p (multiplicity a m)).factorial : ℝ) *
    _ / BinaryCarrierMixedProfile.originalDenominator points action p (multiplicity a m) at h
  simpa only [physicalDegree_eq] using h

include occurrences in
/-- An arbitrary global survival predicate still tests the complete
original physical subgroup. No naturality or factorization of P is needed
for this inclusion into the proved full-profile upper bound. -/
theorem physical_subfamily_card_le_hall {X : Type*}
    (labels : ModelPoints p a m ≃ X) (P : Subgroup (Equiv.Perm X) → Prop) :
    (Nat.card {K : FullOrbitProfileOn (BinaryCarrierMixedProfile.points points)
      (BinaryCarrierMixedProfile.multiplicity p (multiplicity a m))
      (BinaryCarrierMixedProfile.action points action) X // P K.1} : ℝ) ≤
      ((2*p.rank + 4*a + 8*BinaryCarrierOriginalActions.scale m).factorial : ℝ) *
        BinaryCriticalCyclicFourHall.bound p.rank (p.d8+p.e8) a (carrierOrder m) /
          BinaryCarrierMixedProfile.originalDenominator points action p (multiplicity a m) := by
  letI : Fintype X := Fintype.ofEquiv (ModelPoints p a m) labels
  letI : Finite (FullOrbitProfileOn (BinaryCarrierMixedProfile.points points)
      (BinaryCarrierMixedProfile.multiplicity p (multiplicity a m))
      (BinaryCarrierMixedProfile.action points action) X) := by
    unfold FullOrbitProfileOn
    infer_instance
  apply le_trans _ (full_profile_card_le_hall p a m occurrences labels)
  exact_mod_cast Nat.card_le_card_of_injective
    (fun K : {K : FullOrbitProfileOn (BinaryCarrierMixedProfile.points points)
      (BinaryCarrierMixedProfile.multiplicity p (multiplicity a m))
      (BinaryCarrierMixedProfile.action points action) X // P K.1} => K.1)
    Subtype.val_injective

end SymmetricSubgroupAsymptotics.BinaryCarrierOriginalCyclicFourHall
