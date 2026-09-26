import SymmetricSubgroupAsymptotics.BinaryCarrierOriginalCyclicFourHall
import SymmetricSubgroupAsymptotics.BinaryCarrierCyclicFourProductEnergy

/-!
# The carrier reserve on the original thirteen-colour model

The original C4 and twelve carrier actions are exactly those of the Hall
branch. Master inverse images retain every occurrence. The product chart
only separates C4 and orders the carrier occurrences; original normalizers
and multiplicity factorials are unchanged in the physical count.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierOriginalCyclicFourReserve

open BinaryCarrierWord BinaryCarrierOccurrenceWord BinaryCarrierOriginalCyclicFourHall

local instance subgroupFinite {G : Type*} [Group G] [Finite G] :
    Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

attribute [local instance] Fintype.ofFinite

private def exchangeFirstTwo (A B C : Type) [Group A] [Group B] [Group C] :
    (A × (B × C)) ≃* (B × (A × C)) where
  toFun x := (x.2.1, (x.1, x.2.2))
  invFun x := (x.2.1, (x.1, x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable (p : CriticalProfile) (a : ℕ) (m : CarrierTarget → ℕ)

/-- Forget only the separate C4 coordinates, retaining every original
carrier colour and occurrence in the master inverse image. -/
def originalCarrierProjection :
    BinaryCarrierCriticalOccurrence.OriginalProduct p sourceFactor (multiplicity a m) →*
      Carrier m where
  toFun x := fun t => x.2 (some t)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem originalCarrierProjection_full
    (H : Subgroup (BinaryCarrierCriticalOccurrence.OriginalProduct
      p sourceFactor (multiplicity a m)))
    (hH : BinaryCarrierCriticalOccurrence.OriginalFull p sourceFactor (multiplicity a m) H) :
    OccurrenceFull BinaryCarrierOriginalActions.sourceFactor m
      (H.map (originalCarrierProjection p a m)) := by
  intro t j u
  obtain ⟨x, hx⟩ := hH.2 (some t) j u
  obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp x.2
  refine ⟨⟨originalCarrierProjection p a m y,
    Subgroup.mem_map.mpr ⟨y, hy, rfl⟩⟩, ?_⟩
  exact (congrArg
    (fun z : OccurrenceProduct sourceFactor (multiplicity a m) => z (some t) j) hxy).trans hx

variable {L : ℕ} (occurrences : Fin L ≃ (Σ t, Fin (m t)))

/-- This is the same ordered master word used in the original-action
reserve; its equality with the mixed-menu word is already proved. -/
abbrev sourceWord := occurrenceWord BinaryCarrierOriginalActions.sourceFactor m occurrences

/-- The Hall chart followed by the inverse carrier-occurrence chart and
a swap of the first two factors. No original carrier occurrence is merged. -/
def reserveChart :
    BinaryCarrierCriticalOccurrence.OriginalProduct p sourceFactor (multiplicity a m) ≃*
      (Multiplicative (Fin a → ZMod 4) ×
        BinaryCarrierCyclicFourProductEnergy.Exterior p.abelianRank
          (criticalProfileNonabelianChoice p) (sourceWord m occurrences)) :=
  ((hallChart p a m).trans
    ((MulEquiv.refl (CriticalProfileCoordinateGroup p)).prodCongr
      ((MulEquiv.refl (Multiplicative (Fin a → ZMod 4))).prodCongr
        (occurrenceEquiv BinaryCarrierOriginalActions.sourceFactor m occurrences).symm))).trans
      (exchangeFirstTwo _ _ _)

theorem reserveChart_carrier_projection
    (H : Subgroup (BinaryCarrierCriticalOccurrence.OriginalProduct
      p sourceFactor (multiplicity a m))) :
    (SubdirectTailImage.tail ((H.map (reserveChart p a m occurrences).toMonoidHom).map
      (MonoidHom.snd _ _))).map
        (occurrenceEquiv BinaryCarrierOriginalActions.sourceFactor m occurrences).toMonoidHom =
      H.map (originalCarrierProjection p a m) := by
  change (((H.map (reserveChart p a m occurrences).toMonoidHom).map
    (MonoidHom.snd _ _)).map (MonoidHom.snd _ _)).map _ = _
  rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
  apply congrArg (fun f => H.map f)
  apply MonoidHom.ext
  intro x
  change occurrenceEquiv BinaryCarrierOriginalActions.sourceFactor m occurrences
    ((occurrenceEquiv BinaryCarrierOriginalActions.sourceFactor m occurrences).symm
      (fun t => x.2 (some t))) = fun t => x.2 (some t)
  exact (occurrenceEquiv BinaryCarrierOriginalActions.sourceFactor m occurrences).apply_symm_apply _

theorem reserveChart_exterior_full
    (H : Subgroup (BinaryCarrierCriticalOccurrence.OriginalProduct
      p sourceFactor (multiplicity a m)))
    (hH : BinaryCarrierCriticalOccurrence.OriginalFull p sourceFactor (multiplicity a m) H) :
    BinaryCarrierCyclicFourProductEnergy.ExteriorFull p.abelianRank
      (criticalProfileNonabelianChoice p) (sourceWord m occurrences)
      ((H.map (reserveChart p a m occurrences).toMonoidHom).map (MonoidHom.snd _ _)) := by
  constructor
  · apply (occurrenceFull_map_iff BinaryCarrierOriginalActions.sourceFactor m occurrences _).mp
    rw [reserveChart_carrier_projection]
    exact originalCarrierProjection_full p a m H hH
  · have hc := hallChart_critical_full p a m H hH
    intro i
    have he :
        ((H.map (reserveChart p a m occurrences).toMonoidHom).map
          (MonoidHom.snd _ _)).map
            ((criticalProductFactorProjection p.abelianRank
              (criticalProfileNonabelianChoice p) i).comp (MonoidHom.fst _ _)) =
        (H.map (hallChart p a m).toMonoidHom).map
          ((criticalProductFactorProjection p.abelianRank
            (criticalProfileNonabelianChoice p) i).comp (MonoidHom.fst _ _)) := by
      rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [he]
    exact hc i

/-- An embedding of the same original model as the Hall branch into the
proved C4 reserve family. Both critical and carrier fullness are supplied
by the actual original coordinate conditions. -/
def modelEmbeddingReserve
    (P : Subgroup (Equiv.Perm (ModelPoints p a m)) → Prop) :
    ModelFamily p a m P ↪
      BinaryCarrierCyclicFourProductEnergy.OriginalFamily p.abelianRank a
        (criticalProfileNonabelianChoice p) (sourceWord m occurrences) (fun _ => True) :=
  (BinaryCarrierMixedProfileEpimorphism.modelEmbeddingSourceFull
    points action sourceFactor hom hom_surjective p (multiplicity a m) P).trans {
      toFun := fun H => ⟨H.1.map (reserveChart p a m occurrences).toMonoidHom,
        reserveChart_exterior_full p a m occurrences H.1 H.2.1, True.intro⟩
      inj' := by
        intro H K h
        apply Subtype.ext
        apply Subgroup.map_injective (f := (reserveChart p a m occurrences).toMonoidHom)
          (reserveChart p a m occurrences).injective
        exact congrArg
          (fun J : BinaryCarrierCyclicFourProductEnergy.OriginalFamily p.abelianRank a
            (criticalProfileNonabelianChoice p) (sourceWord m occurrences)
            (fun _ => True) => J.1) h }

include occurrences in
/-- The source order cap and every original normal-history row are proved
by the existing eight-master word certificates. No count input is supplied. -/
theorem modelFamily_card_le_reserve
    (P : Subgroup (Equiv.Perm (ModelPoints p a m)) → Prop) :
    (Nat.card (ModelFamily p a m P) : ℝ) ≤
      terminalProductReserve (p.abelianRank+2*a) (criticalProfileNonabelianChoice p)
        12 L (BinaryCarrierOriginalActions.scale m : ℝ) := by
  have h : (Nat.card (ModelFamily p a m P) : ℝ) ≤
      (Nat.card (BinaryCarrierCyclicFourProductEnergy.OriginalFamily p.abelianRank a
        (criticalProfileNonabelianChoice p) (sourceWord m occurrences)
        (fun _ => True)) : ℝ) := by
    exact_mod_cast Nat.card_le_card_of_injective (modelEmbeddingReserve p a m occurrences P)
      (modelEmbeddingReserve p a m occurrences P).injective
  apply h.trans
  simpa only [sourceWord, occurrenceWord_length] using
    BinaryCarrierCyclicFourProductEnergy.originalFamily_card_le_reserve p.abelianRank a
      (criticalProfileNonabelianChoice p) (sourceWord m occurrences) 12
      (BinaryCarrierOriginalActions.occurrenceOrderBound m occurrences)
      (BinaryCarrierOriginalActions.scale m : ℝ)
      (BinaryCarrierOriginalActions.occurrenceHistoryRows m occurrences) (fun _ => True)

include occurrences in
/-- The denominator belongs to all thirteen original physical colours.
Only the model count uses master inverse images and the carrier reserve. -/
theorem full_profile_card_le_reserve {X : Type*}
    (labels : ModelPoints p a m ≃ X) :
    (Nat.card (FullOrbitProfileOn (BinaryCarrierMixedProfile.points points)
      (BinaryCarrierMixedProfile.multiplicity p (multiplicity a m))
      (BinaryCarrierMixedProfile.action points action) X) : ℝ) ≤
      ((2*p.rank+4*a+8*BinaryCarrierOriginalActions.scale m).factorial : ℝ) *
        terminalProductReserve (p.abelianRank+2*a) (criticalProfileNonabelianChoice p)
          12 L (BinaryCarrierOriginalActions.scale m : ℝ) /
            BinaryCarrierMixedProfile.originalDenominator points action p (multiplicity a m) := by
  rw [← Nat.card_congr (assembledFullOrbitProfileEquiv
    (X := X) (m := BinaryCarrierMixedProfile.multiplicity p (multiplicity a m))
    (BinaryCarrierMixedProfile.action points action))]
  have hmodel :
      (Nat.card {K // OrbitProfileFull
        (m := BinaryCarrierMixedProfile.multiplicity p (multiplicity a m))
        (BinaryCarrierMixedProfile.action points action) 1 K} : ℝ) ≤
      terminalProductReserve (p.abelianRank+2*a) (criticalProfileNonabelianChoice p)
        12 L (BinaryCarrierOriginalActions.scale m : ℝ) := by
    simpa only [ModelFamily, BinaryCarrierMixedProfile.ModelFamily, and_true] using
      modelFamily_card_le_reserve p a m occurrences (fun _ => True)
  have h := assembledOrbitProfileOn_card_le_real_of_model_bound
    (orbitProfileFull_family_natural
      (BinaryCarrierMixedProfile.multiplicity p (multiplicity a m))
      (BinaryCarrierMixedProfile.action points action)) labels hmodel
  change _ ≤ ((BinaryCarrierMixedProfile.physicalDegree points p (multiplicity a m)).factorial : ℝ) *
    _ / BinaryCarrierMixedProfile.originalDenominator points action p (multiplicity a m) at h
  simpa only [physicalDegree_eq] using h

include occurrences in
/-- Arbitrary survival remains a predicate on the complete original
physical subgroup; dropping it uses only an injective subtype inclusion. -/
theorem physical_subfamily_card_le_reserve {X : Type*}
    (labels : ModelPoints p a m ≃ X) (P : Subgroup (Equiv.Perm X) → Prop) :
    (Nat.card {K : FullOrbitProfileOn (BinaryCarrierMixedProfile.points points)
      (BinaryCarrierMixedProfile.multiplicity p (multiplicity a m))
      (BinaryCarrierMixedProfile.action points action) X // P K.1} : ℝ) ≤
      ((2*p.rank+4*a+8*BinaryCarrierOriginalActions.scale m).factorial : ℝ) *
        terminalProductReserve (p.abelianRank+2*a) (criticalProfileNonabelianChoice p)
          12 L (BinaryCarrierOriginalActions.scale m : ℝ) /
            BinaryCarrierMixedProfile.originalDenominator points action p (multiplicity a m) := by
  letI : Fintype X := Fintype.ofEquiv (ModelPoints p a m) labels
  letI : Finite (FullOrbitProfileOn (BinaryCarrierMixedProfile.points points)
      (BinaryCarrierMixedProfile.multiplicity p (multiplicity a m))
      (BinaryCarrierMixedProfile.action points action) X) := by
    unfold FullOrbitProfileOn
    infer_instance
  apply le_trans _ (full_profile_card_le_reserve p a m occurrences labels)
  exact_mod_cast Nat.card_le_card_of_injective
    (fun K : {K : FullOrbitProfileOn (BinaryCarrierMixedProfile.points points)
      (BinaryCarrierMixedProfile.multiplicity p (multiplicity a m))
      (BinaryCarrierMixedProfile.action points action) X // P K.1} => K.1)
    Subtype.val_injective

end SymmetricSubgroupAsymptotics.BinaryCarrierOriginalCyclicFourReserve
