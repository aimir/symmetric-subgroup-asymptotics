import SymmetricSubgroupAsymptotics.OddMarkerBinaryContraction
import SymmetricSubgroupAsymptotics.OddCriticalProfiles
import SymmetricSubgroupAsymptotics.BinaryCarrierSmallSupportProfiles
import SymmetricSubgroupAsymptotics.BinaryCarrierS3Actions

/-! Exact contraction of one natural S3 marker over the thirteen original
noncritical colors. The sign quotient adds one original critical C2
occurrence. Every old critical and noncritical occurrence stays full, while
the projection to either complete class product may remain proper. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierS3Model

open BinaryCarrierOriginalCyclicFourHall

abbrev OriginalTail (q : Target → ℕ) := OrbitProfileProductGroup q action
abbrev Exterior (p : CriticalProfile) (q : Target → ℕ) :=
  CriticalOriginalProduct p × OriginalTail q
abbrev Original (p : CriticalProfile) (q : Target → ℕ) :=
  OddMarkerGroup × Exterior p q
abbrev Contracted (p : CriticalProfile) (q : Target → ℕ) :=
  Multiplicative (ZMod 2) × Exterior p q

def ExteriorFull (p : CriticalProfile) (q : Target → ℕ)
    (H : Subgroup (Exterior p q)) : Prop :=
  OrbitProfileProductFull p.multiplicity criticalActionSubgroup
      (H.map (MonoidHom.fst _ _)) ∧
    OrbitProfileProductFull q action (H.map (MonoidHom.snd _ _))

def Full (p : CriticalProfile) (q : Target → ℕ)
    (H : Subgroup (Original p q)) : Prop :=
  H.map (MonoidHom.fst _ _) = ⊤ ∧ ExteriorFull p q (H.map (MonoidHom.snd _ _))

def BinaryFull (p : CriticalProfile) (q : Target → ℕ)
    (H : Subgroup (Contracted p q)) : Prop :=
  H.map (MonoidHom.fst _ _) = ⊤ ∧ ExteriorFull p q (H.map (MonoidHom.snd _ _))

abbrev FullModels (p : CriticalProfile) (q : Target → ℕ) :=
  {H : Subgroup (Original p q) // Full p q H}

abbrev EvenModels (p : CriticalProfile) (q : Target → ℕ) :=
  BinaryCarrierMixedProfile.ModelFamily points action p q (fun _ => True)

/-- Binary structure is proved for the literal target product, independently
of which subgroup is later selected. No master inverse image replaces it. -/
theorem originalTail_binary (q : Target → ℕ) : IsPGroup 2 (OriginalTail q) := by
  let m : CarrierTarget → ℕ := fun t => q (some t)
  let e : Fin (Fintype.card (Σ t, Fin (m t))) ≃ (Σ t, Fin (m t)) :=
    (Fintype.equivFin _).symm
  have h := BinaryCarrierOriginalSmallSupport.tail_binary (q none) m e
  change IsPGroup 2 (OrbitProfileProductGroup
    (multiplicity (q none) (fun t => q (some t))) action) at h
  rw [BinaryCarrierSmallSupportProfiles.multiplicity_split] at h
  exact h

theorem exterior_binary (p : CriticalProfile) (q : Target → ℕ) :
    IsPGroup 2 (Exterior p q) := by
  intro x
  obtain ⟨k, hk⟩ := originalTail_binary q x.2
  refine ⟨k+2, ?_⟩
  apply Prod.ext
  · change x.1 ^ (2^(k+2)) = 1
    rw [pow_add, mul_comm (2^k), pow_mul]
    change (x.1^4)^(2^k) = 1
    rw [criticalOriginalProduct_pow_four, one_pow]
  · change x.2 ^ (2^(k+2)) = 1
    rw [pow_add, pow_mul, hk, one_pow]

/-- Only the literal marker is quotiented; the entire exterior image is fixed. -/
def contractionEquiv (p : CriticalProfile) (q : Target → ℕ) :
    FullModels p q ≃ {H : Subgroup (Contracted p q) // BinaryFull p q H} :=
  oddMarkerBinaryContractionEquiv (exterior_binary p q) (ExteriorFull p q)

/-- The old critical chart installs the marker as the first C2 occurrence;
the complete original noncritical tuple is unchanged. -/
def addC2Chart (p : CriticalProfile) (q : Target → ℕ) :
    Contracted p q ≃* Exterior p.addC2 q :=
  (MulEquiv.prodAssoc :
    ((Multiplicative (ZMod 2) × CriticalOriginalProduct p) × OriginalTail q) ≃*
      (Multiplicative (ZMod 2) × (CriticalOriginalProduct p × OriginalTail q))).symm.trans
      ((criticalAddC2ProductEquiv p).prodCongr (MulEquiv.refl (OriginalTail q)))

private def markerCriticalProjection (p : CriticalProfile) (q : Target → ℕ) :
    Contracted p q →* (Multiplicative (ZMod 2) × CriticalOriginalProduct p) :=
  (MonoidHom.fst _ _).prod ((MonoidHom.fst _ _).comp (MonoidHom.snd _ _))

/-- Coordinate fullness uses the checked critical add-C2 equivalence and
literal projection identities, without requiring full class projections. -/
theorem addC2Chart_full_iff (p : CriticalProfile) (q : Target → ℕ)
    (H : Subgroup (Contracted p q)) :
    ExteriorFull p.addC2 q (H.map (addC2Chart p q).toMonoidHom) ↔ BinaryFull p q H := by
  have hc : (H.map (addC2Chart p q).toMonoidHom).map (MonoidHom.fst _ _) =
      (H.map (markerCriticalProjection p q)).map (criticalAddC2ProductEquiv p).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  have ht : (H.map (addC2Chart p q).toMonoidHom).map (MonoidHom.snd _ _) =
      (H.map (MonoidHom.snd _ _)).map (MonoidHom.snd _ _) := by
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  have hm : (H.map (markerCriticalProjection p q)).map (MonoidHom.fst _ _) =
      H.map (MonoidHom.fst _ _) := by
    rw [Subgroup.map_map]
    rfl
  have ho : (H.map (markerCriticalProjection p q)).map (MonoidHom.snd _ _) =
      (H.map (MonoidHom.snd _ _)).map (MonoidHom.fst _ _) := by
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  unfold BinaryFull ExteriorFull
  rw [hc, ht, criticalAddC2Product_full_iff]
  unfold MarkerProductFull
  rw [hm, ho]
  exact and_assoc

def addC2FullEquiv (p : CriticalProfile) (q : Target → ℕ) :
    {H : Subgroup (Contracted p q) // BinaryFull p q H} ≃
      {H : Subgroup (Exterior p.addC2 q) // ExteriorFull p.addC2 q H} where
  toFun H := ⟨H.1.map (addC2Chart p q).toMonoidHom,
    (addC2Chart_full_iff p q H.1).mpr H.2⟩
  invFun H := ⟨H.1.comap (addC2Chart p q).toMonoidHom, by
    apply (addC2Chart_full_iff p q _).mp
    rw [Subgroup.map_comap_eq_self_of_surjective (addC2Chart p q).surjective]
    exact H.2⟩
  left_inv H := Subtype.ext (Subgroup.comap_map_eq_self_of_injective
    (addC2Chart p q).injective H.1)
  right_inv H := Subtype.ext (Subgroup.map_comap_eq_self_of_surjective
    (addC2Chart p q).surjective H.1)

/-- Faithful original permutation models and their literal split product
are exactly equivalent, including each regular critical coordinate. -/
def evenModelEquivSplit (p : CriticalProfile) (q : Target → ℕ) :
    EvenModels p q ≃ {H : Subgroup (Exterior p q) // ExteriorFull p q H} :=
  (BinaryCarrierMixedProfile.modelEquivSplit points action
    (fun t => (sourceFactor t).binary.of_surjective (hom t) (hom_surjective t)) p q
      (fun _ => True)).trans (Equiv.subtypeEquivRight (fun H => by
        change (ExteriorFull p q H ∧ True) ↔ ExteriorFull p q H
        simp))

/-- Exact model contraction: q and all its original colors are unchanged. -/
def fullModelEquiv (p : CriticalProfile) (q : Target → ℕ) :
    FullModels p q ≃ EvenModels p.addC2 q :=
  (contractionEquiv p q).trans
    ((addC2FullEquiv p q).trans (evenModelEquivSplit p.addC2 q).symm)

/-- Any full original predicate is retained on its exact inverse subgroup. -/
def filteredModelEquiv (p : CriticalProfile) (q : Target → ℕ)
    (P : Subgroup (Original p q) → Prop) :
    {H : Subgroup (Original p q) // Full p q H ∧ P H} ≃
      {K : EvenModels p.addC2 q // P ((fullModelEquiv p q).symm K).1} :=
  (Equiv.subtypeSubtypeEquivSubtypeInter (Full p q) P).symm.trans
    (fullModelEquiv p q).subtypeEquivOfSubtype'

theorem fullModel_card (p : CriticalProfile) (q : Target → ℕ) :
    Nat.card (FullModels p q) = Nat.card (EvenModels p.addC2 q) :=
  Nat.card_congr (fullModelEquiv p q)

theorem fullModel_count (p : CriticalProfile) (q : Target → ℕ) :
    (Nat.card (FullModels p q) : ℝ) =
      BinaryCarrierSmallSupportProfiles.modelCount p.addC2 q := by
  change (Nat.card (FullModels p q) : ℝ) = (Nat.card (EvenModels p.addC2 q) : ℝ)
  exact_mod_cast fullModel_card p q


abbrev OddCriticalOriginal (p : CriticalProfile) :=
  OrbitProfileProductGroup (oddCriticalMultiplicity true p) oddCriticalActionSubgroup

/-- Split the one original marker from the original odd-critical tuple,
keeping the full original carrier tuple as the final factor. -/
def oddProductChart (p : CriticalProfile) (q : Target → ℕ) :
    (OddCriticalOriginal p × OriginalTail q) ≃* Original p q :=
  ((oddS3OriginalProductEquiv p).prodCongr (MulEquiv.refl (OriginalTail q))).trans
    (MulEquiv.prodAssoc : ((OddMarkerGroup × CriticalOriginalProduct p) × OriginalTail q) ≃*
      (OddMarkerGroup × (CriticalOriginalProduct p × OriginalTail q)))

theorem oddProductChart_full_iff (p : CriticalProfile) (q : Target → ℕ)
    (H : Subgroup (OddCriticalOriginal p × OriginalTail q)) :
    Full p q (H.map (oddProductChart p q).toMonoidHom) ↔
      OrbitProfileProductFull (oddCriticalMultiplicity true p) oddCriticalActionSubgroup
          (H.map (MonoidHom.fst _ _)) ∧
        OrbitProfileProductFull q action (H.map (MonoidHom.snd _ _)) := by
  have hm : (H.map (oddProductChart p q).toMonoidHom).map (MonoidHom.fst _ _) =
      ((H.map (MonoidHom.fst _ _)).map (oddS3OriginalProductEquiv p).toMonoidHom).map
        (MonoidHom.fst _ _) := by
    simp only [Subgroup.map_map]
    rfl
  have hc : ((H.map (oddProductChart p q).toMonoidHom).map
      (MonoidHom.snd _ _)).map (MonoidHom.fst _ _) =
      ((H.map (MonoidHom.fst _ _)).map (oddS3OriginalProductEquiv p).toMonoidHom).map
        (MonoidHom.snd _ _) := by
    simp only [Subgroup.map_map]
    rfl
  have ht : ((H.map (oddProductChart p q).toMonoidHom).map
      (MonoidHom.snd _ _)).map (MonoidHom.snd _ _) = H.map (MonoidHom.snd _ _) := by
    simp only [Subgroup.map_map]
    rfl
  rw [oddS3OriginalProduct_full_iff]
  unfold Full ExteriorFull MarkerProductFull
  rw [hm, hc, ht]
  exact and_assoc.symm

abbrev ActionProduct (p : CriticalProfile) (q : Target → ℕ) :=
  OrbitProfileProductGroup (BinaryCarrierS3Actions.multiplicity p q) BinaryCarrierS3Actions.action

def originalProductChart (p : CriticalProfile) (q : Target → ℕ) :
    ActionProduct p q ≃* Original p q :=
  (OrbitProfileProductSum.equiv (BinaryCarrierS3Actions.multiplicity p q)
    BinaryCarrierS3Actions.action).trans (oddProductChart p q)

theorem originalProductChart_full_iff (p : CriticalProfile) (q : Target → ℕ)
    (H : Subgroup (ActionProduct p q)) :
    Full p q (H.map (originalProductChart p q).toMonoidHom) ↔
      OrbitProfileProductFull (BinaryCarrierS3Actions.multiplicity p q)
        BinaryCarrierS3Actions.action H := by
  change Full p q (H.map ((oddProductChart p q).toMonoidHom.comp
    (OrbitProfileProductSum.equiv (BinaryCarrierS3Actions.multiplicity p q)
      BinaryCarrierS3Actions.action).toMonoidHom)) ↔ _
  rw [← Subgroup.map_map, oddProductChart_full_iff]
  exact OrbitProfileProductSum.splitFull_map_iff
    (BinaryCarrierS3Actions.multiplicity p q) BinaryCarrierS3Actions.action H

def originalProductFullEquiv (p : CriticalProfile) (q : Target → ℕ) :
    {H : Subgroup (ActionProduct p q) //
      OrbitProfileProductFull (BinaryCarrierS3Actions.multiplicity p q)
        BinaryCarrierS3Actions.action H} ≃ FullModels p q where
  toFun H := ⟨H.1.map (originalProductChart p q).toMonoidHom,
    (originalProductChart_full_iff p q H.1).mpr H.2⟩
  invFun H := ⟨H.1.comap (originalProductChart p q).toMonoidHom, by
    apply (originalProductChart_full_iff p q _).mp
    rw [Subgroup.map_comap_eq_self_of_surjective (originalProductChart p q).surjective]
    exact H.2⟩
  left_inv H := Subtype.ext (Subgroup.comap_map_eq_self_of_injective
    (originalProductChart p q).injective H.1)
  right_inv H := Subtype.ext (Subgroup.map_comap_eq_self_of_surjective
    (originalProductChart p q).surjective H.1)

/-- The actual original permutation subgroup, with all original blocks,
contracts exactly to the model with one new C2 and unchanged q. -/
def modelEquiv (p : CriticalProfile) (q : Target → ℕ) :
    BinaryCarrierS3Actions.ModelFamily p q ≃ EvenModels p.addC2 q :=
  (orbitProfileProductFullEquiv (BinaryCarrierS3Actions.multiplicity p q)
    BinaryCarrierS3Actions.action).symm.trans
      ((originalProductFullEquiv p q).trans (fullModelEquiv p q))

/-- Arbitrary original survival conditions are evaluated after exact inverse
reconstruction of the original permutation subgroup. -/
def modelPredicateEquiv (p : CriticalProfile) (q : Target → ℕ)
    (P : Subgroup (Equiv.Perm (BinaryCarrierS3Actions.ModelPoints p q)) → Prop) :
    {H : BinaryCarrierS3Actions.ModelFamily p q // P H.1} ≃
      {K : EvenModels p.addC2 q // P ((modelEquiv p q).symm K).1} :=
  (modelEquiv p q).subtypeEquivOfSubtype'

theorem modelEquiv_reconstruct (p : CriticalProfile) (q : Target → ℕ)
    (H : BinaryCarrierS3Actions.ModelFamily p q) :
    ((modelEquiv p q).symm (modelEquiv p q H)).1 = H.1 :=
  congrArg Subtype.val ((modelEquiv p q).symm_apply_apply H)

theorem model_card (p : CriticalProfile) (q : Target → ℕ) :
    Nat.card (BinaryCarrierS3Actions.ModelFamily p q) = Nat.card (EvenModels p.addC2 q) :=
  Nat.card_congr (modelEquiv p q)

/-- The fixed-model identity has no supplied count bound. Original physical
normalizers and factorials are handled separately on their original points. -/
theorem model_count (p : CriticalProfile) (q : Target → ℕ) :
    (Nat.card (BinaryCarrierS3Actions.ModelFamily p q) : ℝ) =
      BinaryCarrierSmallSupportProfiles.modelCount p.addC2 q := by
  change (Nat.card (BinaryCarrierS3Actions.ModelFamily p q) : ℝ) =
    (Nat.card (EvenModels p.addC2 q) : ℝ)
  exact_mod_cast model_card p q

end SymmetricSubgroupAsymptotics.BinaryCarrierS3Model
