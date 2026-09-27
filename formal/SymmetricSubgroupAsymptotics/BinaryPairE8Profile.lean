import SymmetricSubgroupAsymptotics.BinaryFourPairE8MergeModel

/-!
# The original pair/E8 profile chart

The old E8 occurrences are one distinguished original action colour, not a
tagged copy of that colour.  This file splits that colour from an arbitrary
exterior profile and identifies the selected four-pair cover with the target
profile having one fewer block of four pairs and one more E8 occurrence.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.BinaryPairE8Profile

open RepeatedMarkerMergedProfile

abbrev E8 := BinaryFourPairE8Model.E8

variable {α : Type} [Fintype α] (Ω : α → Type)
    [∀ a, Fintype (Ω a)] [∀ a, Nonempty (Ω a)]
    (m : α → ℕ) (U : ∀ a, Subgroup (Equiv.Perm (Ω a)))

abbrev ExteriorIndex := PUnit.{1} ⊕ α

def exteriorPoints : ExteriorIndex (α := α) → Type
  | .inl _ => criticalActionPoints .e8
  | .inr a => Ω a

instance (i : ExteriorIndex (α := α)) : Fintype (exteriorPoints Ω i) := by
  cases i <;> dsimp [exteriorPoints] <;> infer_instance

instance (i : ExteriorIndex (α := α)) : Nonempty (exteriorPoints Ω i) := by
  cases i <;> dsimp [exteriorPoints] <;> infer_instance

def exteriorAction : (i : ExteriorIndex (α := α)) →
    Subgroup (Equiv.Perm (exteriorPoints Ω i))
  | .inl _ => criticalActionSubgroup .e8
  | .inr a => U a

def exteriorMultiplicity (e : ℕ) : ExteriorIndex (α := α) → ℕ
  | .inl _ => e
  | .inr a => m a

abbrev BaseExterior := OrbitProfileProductGroup m U

abbrev Exterior (e : ℕ) :=
  OrbitProfileProductGroup (exteriorMultiplicity m e) (exteriorAction Ω U)

/-- Split the actual E8 colour from the untouched original exterior. -/
def exteriorChart (e : ℕ) :
    Exterior Ω m U e ≃* ((Fin e → E8) × BaseExterior Ω m U) where
  toFun f := (fun j => f (.inl PUnit.unit) j, fun a => f (.inr a))
  invFun f i := match i with
    | .inl _ => f.1
    | .inr a => f.2 a
  left_inv f := by funext i j; cases i <;> rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem exterior_full_iff (e : ℕ) (K : Subgroup (Exterior Ω m U e)) :
    OrbitProfileProductFull (exteriorMultiplicity m e) (exteriorAction Ω U) K ↔
      BinaryFourPairE8MergeModel.OldPredicate e (OrbitProfileProductFull m U)
        (K.map (exteriorChart Ω m U e).toMonoidHom) := by
  constructor
  · intro h
    constructor
    · intro j
      apply top_unique
      intro z _
      obtain ⟨x,hx⟩ := h (.inl PUnit.unit) j z
      exact Subgroup.mem_map.mpr ⟨exteriorChart Ω m U e x.val,
        Subgroup.mem_map.mpr ⟨x.val,x.property,rfl⟩,hx⟩
    · intro a j u
      obtain ⟨x,hx⟩ := h (.inr a) j u
      exact ⟨⟨(exteriorChart Ω m U e x.val).2,
        Subgroup.mem_map.mpr ⟨exteriorChart Ω m U e x.val,
          Subgroup.mem_map.mpr ⟨x.val,x.property,rfl⟩,rfl⟩⟩,hx⟩
  · rintro ⟨h8,hD⟩ i j u
    cases i with
    | inl i =>
      cases i
      change Fin e at j
      change E8 at u
      have hu : u ∈ (K.map (exteriorChart Ω m U e).toMonoidHom).map
          (BinaryFourPairE8MergeModel.oldE8Coordinate e j) := by
        rw [h8]
        trivial
      obtain ⟨y,hy,he⟩ := Subgroup.mem_map.mp hu
      obtain ⟨x,hx,hxy⟩ := Subgroup.mem_map.mp hy
      refine ⟨⟨x,hx⟩,?_⟩
      change x (.inl PUnit.unit) j = u
      have hxy' := congrArg (fun w : (Fin e → E8) × BaseExterior Ω m U => w.1 j) hxy
      exact hxy'.trans he
    | inr a =>
      obtain ⟨y,hy⟩ := hD a j u
      obtain ⟨z,hz,he⟩ := Subgroup.mem_map.mp y.property
      obtain ⟨x,hx,hxz⟩ := Subgroup.mem_map.mp hz
      refine ⟨⟨x,hx⟩,?_⟩
      change x (.inr a) j = u
      have hxz' := congrArg
        (fun w : (Fin e → E8) × BaseExterior Ω m U => w.2 a j) hxz
      have he' := congrArg (fun w : BaseExterior Ω m U => w a j) he
      exact hxz'.trans (he'.trans hy)

abbrev SourceCover (n e : ℕ) :=
  BinaryFourPairSelectedModel.CoverFamily (D := Exterior Ω m U e) n
    (OrbitProfileProductFull (exteriorMultiplicity m e) (exteriorAction Ω U))

/-- Apply the E8/exterior split only inside the retained exterior. -/
def coverChart (n e : ℕ) :
    BinaryFourPairSelectedModel.Covered (D := Exterior Ω m U e) n ≃*
      BinaryFourPairE8MergeModel.Source (D := BaseExterior Ω m U) n e :=
  (MulEquiv.refl E8).prodCongr
    ((MulEquiv.refl (Fin n → BinaryFourPairE8Model.Sign)).prodCongr
      (exteriorChart Ω m U e))

theorem coverChart_family_iff (n e : ℕ)
    (K : Subgroup (BinaryFourPairSelectedModel.Covered
      (D := Exterior Ω m U e) n)) :
    (K.map (coverChart Ω m U n e).toMonoidHom).map
          (MonoidHom.fst E8 _) = ⊤ ∧
      (∀ j, (K.map (coverChart Ω m U n e).toMonoidHom).map
        (BinaryFourPairSelectedModel.retainedCoordinate j) = ⊤) ∧
      BinaryFourPairE8MergeModel.OldPredicate e (OrbitProfileProductFull m U)
        ((K.map (coverChart Ω m U n e).toMonoidHom).map
          (BinaryFourPairSelectedModel.exterior n)) ↔
    K.map (MonoidHom.fst E8 _) = ⊤ ∧
      (∀ j, K.map (BinaryFourPairSelectedModel.retainedCoordinate j) = ⊤) ∧
      OrbitProfileProductFull (exteriorMultiplicity m e) (exteriorAction Ω U)
        (K.map (BinaryFourPairSelectedModel.exterior n)) := by
  have hnew :
      (K.map (coverChart Ω m U n e).toMonoidHom).map (MonoidHom.fst E8 _) =
        K.map (MonoidHom.fst E8 _) := by
    simp only [Subgroup.map_map]
    rfl
  have hpair (j : Fin n) :
      (K.map (coverChart Ω m U n e).toMonoidHom).map
          (BinaryFourPairSelectedModel.retainedCoordinate j) =
        K.map (BinaryFourPairSelectedModel.retainedCoordinate j) := by
    simp only [Subgroup.map_map]
    rfl
  have hext :
      (K.map (coverChart Ω m U n e).toMonoidHom).map
          (BinaryFourPairSelectedModel.exterior n) =
        (K.map (BinaryFourPairSelectedModel.exterior n)).map
          (exteriorChart Ω m U e).toMonoidHom := by
    simp only [Subgroup.map_map]
    rfl
  rw [hnew]
  simp_rw [hpair]
  rw [hext, ← exterior_full_iff Ω m U e]

def sourceCoverEquiv (n e : ℕ) :
    SourceCover Ω m U n e ≃
      BinaryFourPairE8MergeModel.CoverFamily
        (D := BaseExterior Ω m U) n e (OrbitProfileProductFull m U) :=
  (coverChart Ω m U n e).mapSubgroup.toEquiv.subtypeEquiv (fun K => by
    simpa only [MulEquiv.coe_mapSubgroup] using
      (coverChart_family_iff Ω m U n e K).symm)

abbrev TargetSignFamily (n e : ℕ) :=
  BinaryDuplicatePairProfile.SignFamily
    (exteriorPoints Ω) (exteriorMultiplicity m e) (exteriorAction Ω U) n

/-- Coordinate presentation of the ordinary target profile with `e` actual
E8 occurrences. -/
def targetChart (n e : ℕ) :
    ((Fin n → BinaryFourPairE8Model.Sign) × Exterior Ω m U e) ≃*
      ((Fin n → BinaryFourPairE8Model.Sign) ×
        ((Fin e → E8) × BaseExterior Ω m U)) :=
  (MulEquiv.refl (Fin n → BinaryFourPairE8Model.Sign)).prodCongr
    (exteriorChart Ω m U e)

def profilePairCoordinate {D : Type*} [Group D] (n e : ℕ) (j : Fin n) :
    ((Fin n → BinaryFourPairE8Model.Sign) × ((Fin e → E8) × D)) →*
      BinaryFourPairE8Model.Sign where
  toFun x := x.1 j
  map_one' := rfl
  map_mul' _ _ := rfl

def profileE8Coordinate {D : Type*} [Group D] (n e : ℕ) (j : Fin e) :
    ((Fin n → BinaryFourPairE8Model.Sign) × ((Fin e → E8) × D)) →* E8 where
  toFun x := x.2.1 j
  map_one' := rfl
  map_mul' _ _ := rfl

def profileExterior {D : Type*} [Group D] (n e : ℕ) :
    ((Fin n → BinaryFourPairE8Model.Sign) × ((Fin e → E8) × D)) →* D where
  toFun x := x.2.2
  map_one' := rfl
  map_mul' _ _ := rfl

theorem coordinate_map_eq_top_iff {D : Type*} [Group D]
    {n : ℕ} (K : Subgroup ((Fin n → BinaryFourPairE8Model.Sign) × D)) (j : Fin n) :
    K.map (BinaryFourPairSelectedModel.coordinate j) = ⊤ ↔
      Function.Surjective (RepeatedCharacterCollapse.character K j) := by
  constructor
  · intro h z
    have hz : z ∈ K.map (BinaryFourPairSelectedModel.coordinate j) := by
      rw [h]
      trivial
    obtain ⟨x,hx,he⟩ := Subgroup.mem_map.mp hz
    exact ⟨⟨x,hx⟩,he⟩
  · intro h
    apply top_unique
    intro z _
    obtain ⟨x,hx⟩ := h z
    exact Subgroup.mem_map.mpr ⟨x.val,x.property,hx⟩

theorem targetChart_family_iff (n e : ℕ)
    (K : Subgroup ((Fin n → BinaryFourPairE8Model.Sign) × Exterior Ω m U e)) :
    (∀ j, (K.map (targetChart Ω m U n e).toMonoidHom).map
        (profilePairCoordinate (D := BaseExterior Ω m U) n e j) = ⊤) ∧
      (∀ j : Fin e, (K.map (targetChart Ω m U n e).toMonoidHom).map
        (profileE8Coordinate (D := BaseExterior Ω m U) n e j) = ⊤) ∧
      OrbitProfileProductFull m U
        ((K.map (targetChart Ω m U n e).toMonoidHom).map
          (profileExterior (D := BaseExterior Ω m U) n e)) ↔
    (∀ j, Function.Surjective (RepeatedCharacterCollapse.character K j)) ∧
      OrbitProfileProductFull (exteriorMultiplicity m e) (exteriorAction Ω U)
        (K.map (MonoidHom.snd (Fin n → BinaryFourPairE8Model.Sign) _)) := by
  have hp (j : Fin n) :
      (K.map (targetChart Ω m U n e).toMonoidHom).map
          (profilePairCoordinate (D := BaseExterior Ω m U) n e j) =
        K.map (BinaryFourPairSelectedModel.coordinate j) := by
    simp only [Subgroup.map_map]
    rfl
  have hext :
      BinaryFourPairE8MergeModel.OldPredicate e (OrbitProfileProductFull m U)
        ((K.map (targetChart Ω m U n e).toMonoidHom).map
          (MonoidHom.snd (Fin n → BinaryFourPairE8Model.Sign) _)) ↔
      OrbitProfileProductFull (exteriorMultiplicity m e) (exteriorAction Ω U)
        (K.map (MonoidHom.snd (Fin n → BinaryFourPairE8Model.Sign) _)) := by
    have hm :
        (K.map (targetChart Ω m U n e).toMonoidHom).map
            (MonoidHom.snd (Fin n → BinaryFourPairE8Model.Sign) _) =
          (K.map (MonoidHom.snd (Fin n → BinaryFourPairE8Model.Sign) _)).map
            (exteriorChart Ω m U e).toMonoidHom := by
      simp only [Subgroup.map_map]
      rfl
    rw [hm, ← exterior_full_iff Ω m U e]
  have hold :
      ((∀ j : Fin e, (K.map (targetChart Ω m U n e).toMonoidHom).map
          (profileE8Coordinate (D := BaseExterior Ω m U) n e j) = ⊤) ∧
        OrbitProfileProductFull m U
          ((K.map (targetChart Ω m U n e).toMonoidHom).map
            (profileExterior (D := BaseExterior Ω m U) n e))) ↔
      BinaryFourPairE8MergeModel.OldPredicate e (OrbitProfileProductFull m U)
        ((K.map (targetChart Ω m U n e).toMonoidHom).map
          (MonoidHom.snd (Fin n → BinaryFourPairE8Model.Sign) _)) := by
    simp only [BinaryFourPairE8MergeModel.OldPredicate, Subgroup.map_map]
    rfl
  rw [hold, hext]
  constructor
  · rintro ⟨hp',hfull⟩
    exact ⟨fun j => (coordinate_map_eq_top_iff K j).mp (by rw [← hp j]; exact hp' j),hfull⟩
  · rintro ⟨hp',hfull⟩
    exact ⟨fun j => by rw [hp j]; exact (coordinate_map_eq_top_iff K j).mpr (hp' j),hfull⟩

/-- The merged coordinate family is exactly the ordinary target profile;
the head coordinate is not a new action colour. -/
def targetSignEquivMerged (n e : ℕ) :
    TargetSignFamily Ω m U n (e+1) ≃
      BinaryFourPairE8MergeModel.MergedFamily
        (D := BaseExterior Ω m U) n e (OrbitProfileProductFull m U) :=
  (targetChart Ω m U n (e+1)).mapSubgroup.toEquiv.subtypeEquiv (fun K => by
    simpa only [MulEquiv.coe_mapSubgroup] using
      (targetChart_family_iff Ω m U n (e+1) K).symm)

/-- Complete coordinate-level comparison used by the profile weight: every
selected cover is a subgroup in the ordinary target profile. -/
def sourceCoverEquivTarget (n e : ℕ) :
    SourceCover Ω m U n e ≃ TargetSignFamily Ω m U n (e+1) :=
  (sourceCoverEquiv Ω m U n e).trans
    ((BinaryFourPairE8MergeModel.familyEquiv n e (OrbitProfileProductFull m U)).trans
      (targetSignEquivMerged Ω m U n e).symm)

theorem sourceCover_card (n e : ℕ) :
    Nat.card (SourceCover Ω m U n e) =
      Nat.card (TargetSignFamily Ω m U n (e+1)) :=
  Nat.card_congr (sourceCoverEquivTarget Ω m U n e)

end SymmetricSubgroupAsymptotics.BinaryPairE8Profile
