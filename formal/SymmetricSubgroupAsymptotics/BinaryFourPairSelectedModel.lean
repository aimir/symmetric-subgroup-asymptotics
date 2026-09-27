import SymmetricSubgroupAsymptotics.BinaryFourPairE8Model
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Set

/-!
# Actual ordered selections of four original pair coordinates

Each selected ordered four-tuple is kept as part of the target mark. Its
complement chart retains every other original pair, and the full original
exterior is unchanged. Original character independence supplies the full
E8 projection. The inverse quotient recovers the entire original subgroup,
so arbitrary original predicates remain true after reconstruction.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.BinaryFourPairSelectedModel

open BinaryFourPairE8Model (Sign Four E8)

abbrev Selection (n : ℕ) := Fin 4 ↪ Fin (n + 4)
abbrev Remaining {n : ℕ} (v : Selection n) :=
  {j : Fin (n + 4) // j ∉ Set.range v}

theorem remaining_card {n : ℕ} (v : Selection n) :
    Fintype.card (Remaining v) = n := by
  rw [Fintype.card_subtype_compl]
  have hr : Fintype.card (Set.range v) = 4 := by
    rw [← Fintype.card_congr (Equiv.ofInjective v v.injective), Fintype.card_fin]
  rw [Fintype.card_fin, hr]
  omega

def remainingEquiv {n : ℕ} (v : Selection n) : Remaining v ≃ Fin n :=
  Fintype.equivFinOfCardEq (remaining_card v)

/-- The selected labels occur in exactly their prescribed order. -/
def pointChart {n : ℕ} (v : Selection n) : Fin 4 ⊕ Fin n ≃ Fin (n + 4) :=
  (Equiv.sumCongr (Equiv.ofInjective v v.injective) (remainingEquiv v).symm).trans
    (Equiv.sumCompl (fun j => j ∈ Set.range v))

@[simp] theorem pointChart_selected {n : ℕ} (v : Selection n) (i : Fin 4) :
    pointChart v (Sum.inl i) = v i := rfl

@[simp] theorem pointChart_symm_selected {n : ℕ} (v : Selection n) (i : Fin 4) :
    (pointChart v).symm (v i) = Sum.inl i :=
  (pointChart v).symm_apply_apply (Sum.inl i)

theorem selection_card (n : ℕ) :
    Nat.card (Selection n) = (n + 4).descFactorial 4 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq]
  simp only [Fintype.card_fin]

variable {D : Type*} [Group D]

abbrev Original (n : ℕ) := (Fin (n + 4) → Sign) × D
abbrev Tail (n : ℕ) := (Fin n → Sign) × D
abbrev Covered (n : ℕ) := E8 × Tail (D := D) n

/-- An actual reindexing of the original coordinate product, fixing D. -/
def chart {n : ℕ} (v : Selection n) : Original (D := D) n ≃* Four × Tail (D := D) n where
  toFun x := (fun i => x.1 (v i), (fun j => x.1 (pointChart v (Sum.inr j)), x.2))
  invFun y := (fun j => Sum.elim y.1 y.2.1 ((pointChart v).symm j), y.2.2)
  left_inv x := by
    apply Prod.ext
    · funext j
      obtain ⟨s, rfl⟩ := (pointChart v).surjective j
      cases s <;> simp
    · rfl
  right_inv y := by
    apply Prod.ext
    · funext i
      change Sum.elim y.1 y.2.1 ((pointChart v).symm (pointChart v (Sum.inl i))) = y.1 i
      simp
    · apply Prod.ext
      · funext j
        simp
      · rfl
  map_mul' x y := rfl

@[simp] theorem chart_symm_selected {n : ℕ} (v : Selection n)
    (y : Four × Tail (D := D) n) (i : Fin 4) :
    ((chart v).symm y).1 (v i) = y.1 i := by
  exact congrArg (fun z : Four × Tail (D := D) n => z.1 i)
    ((chart v).apply_symm_apply y)

@[simp] theorem chart_symm_remaining {n : ℕ} (v : Selection n)
    (y : Four × Tail (D := D) n) (j : Fin n) :
    ((chart v).symm y).1 (pointChart v (Sum.inr j)) = y.2.1 j := by
  exact congrArg (fun z : Four × Tail (D := D) n => z.2.1 j)
    ((chart v).apply_symm_apply y)

@[simp] theorem chart_symm_exterior {n : ℕ} (v : Selection n)
    (y : Four × Tail (D := D) n) : ((chart v).symm y).2 = y.2.2 := rfl

def coordinate {I : Type*} (i : I) : ((I → Sign) × D) →* Sign where
  toFun x := x.1 i
  map_one' := rfl
  map_mul' _ _ := rfl

def retainedCoordinate {n : ℕ} (j : Fin n) : Covered (D := D) n →* Sign :=
  (coordinate j).comp (MonoidHom.snd E8 (Tail (D := D) n))

def exterior (n : ℕ) : Covered (D := D) n →* D :=
  (MonoidHom.snd (Fin n → Sign) D).comp (MonoidHom.snd E8 (Tail (D := D) n))

def character {n : ℕ} (H : Subgroup (Original (D := D) n))
    (j : Fin (n + 4)) : PrimeCharacters 2 H where
  toFun g := (g.toMul.val.1 j).toAdd
  map_zero' := rfl
  map_add' _ _ := rfl

def Independent {n : ℕ} (v : Selection n) (H : Subgroup (Original (D := D) n)) : Prop :=
  LinearIndependent (ZMod 2) (fun i => character H (v i))

def joint {n : ℕ} (v : Selection n) (H : Subgroup (Original (D := D) n)) : H →* Four where
  toFun g i := g.val.1 (v i)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem joint_surjective [Finite D] {n : ℕ} (v : Selection n)
    (H : Subgroup (Original (D := D) n)) (hH : Independent v H) :
    Function.Surjective (joint v H) :=
  IndependentCharacterCoordinates.binary_joint_surjective (fun i => character H (v i)) hH

/-- The exact original quotient, including the selected complement chart. -/
def productMap {n : ℕ} (v : Selection n) : Covered (D := D) n →* Original (D := D) n :=
  (chart v).symm.toMonoidHom.comp BinaryFourPairE8Model.productMap

theorem productMap_surjective {n : ℕ} (v : Selection n) :
    Function.Surjective (productMap (D := D) v) :=
  (chart v).symm.surjective.comp BinaryFourPairE8Model.productMap_surjective

@[simp] theorem productMap_selected {n : ℕ} (v : Selection n)
    (y : Covered (D := D) n) (i : Fin 4) :
    (productMap v y).1 (v i) = BinaryFourPairE8Model.quotient y.1 i :=
  chart_symm_selected v _ i

@[simp] theorem productMap_remaining {n : ℕ} (v : Selection n)
    (y : Covered (D := D) n) (j : Fin n) :
    (productMap v y).1 (pointChart v (Sum.inr j)) = y.2.1 j :=
  chart_symm_remaining v _ j

@[simp] theorem productMap_exterior {n : ℕ} (v : Selection n)
    (y : Covered (D := D) n) : (productMap v y).2 = y.2.2 := rfl

def lift {n : ℕ} (v : Selection n) (H : Subgroup (Original (D := D) n)) :
    Subgroup (Covered (D := D) n) := H.comap (productMap v)

theorem reconstruct {n : ℕ} (v : Selection n) (H : Subgroup (Original (D := D) n)) :
    (lift v H).map (productMap v) = H :=
  Subgroup.map_comap_eq_self_of_surjective (productMap_surjective v) H

theorem lift_full [Finite D] {n : ℕ} (v : Selection n)
    (H : Subgroup (Original (D := D) n)) (hH : Independent v H) :
    (lift v H).map (MonoidHom.fst E8 (Tail (D := D) n)) = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨x, hx⟩ := joint_surjective v H hH (BinaryFourPairE8Model.quotient g)
  refine Subgroup.mem_map.mpr ⟨(g, (chart v x.val).2), ?_, rfl⟩
  change (chart v).symm (BinaryFourPairE8Model.quotient g, (chart v x.val).2) ∈ H
  have he : (BinaryFourPairE8Model.quotient g, (chart v x.val).2) = chart v x.val :=
    Prod.ext hx.symm rfl
  rw [he, MulEquiv.symm_apply_apply]
  exact x.property

theorem retained_image {n : ℕ} (v : Selection n)
    (H : Subgroup (Original (D := D) n)) (j : Fin n) :
    (lift v H).map (retainedCoordinate j) =
      H.map (coordinate (pointChart v (Sum.inr j))) := by
  calc
    _ = ((lift v H).map (productMap v)).map
        (coordinate (pointChart v (Sum.inr j))) := by
      rw [Subgroup.map_map]
      congr 1
      apply MonoidHom.ext
      intro y
      exact (productMap_remaining v y j).symm
    _ = _ := by rw [reconstruct]

theorem exterior_image {n : ℕ} (v : Selection n) (H : Subgroup (Original (D := D) n)) :
    (lift v H).map (exterior n) = H.map (MonoidHom.snd (Fin (n + 4) → Sign) D) := by
  calc
    _ = ((lift v H).map (productMap v)).map
        (MonoidHom.snd (Fin (n + 4) → Sign) D) := by
      rw [Subgroup.map_map]
      rfl
    _ = _ := by rw [reconstruct]

def Full {n : ℕ} (H : Subgroup (Original (D := D) n)) : Prop :=
  ∀ j, H.map (coordinate j) = ⊤

abbrev OriginalFamily (n : ℕ) (P : Subgroup D → Prop)
    (R : Subgroup (Original (D := D) n) → Prop) :=
  {H : Subgroup (Original (D := D) n) // Full H ∧
    P (H.map (MonoidHom.snd (Fin (n + 4) → Sign) D)) ∧ R H}

abbrev SelectedFamily {n : ℕ} (v : Selection n) (P : Subgroup D → Prop)
    (R : Subgroup (Original (D := D) n) → Prop) :=
  {H : OriginalFamily n P R // Independent v H.val}

abbrev CoverFamily (n : ℕ) (P : Subgroup D → Prop) :=
  {K : Subgroup (Covered (D := D) n) //
    K.map (MonoidHom.fst E8 (Tail (D := D) n)) = ⊤ ∧
      (∀ j, K.map (retainedCoordinate j) = ⊤) ∧ P (K.map (exterior n))}

/-- All retained pair projections and the whole exterior predicate remain
on the original coordinates. R is recovered by the literal quotient. -/
def selectedEmbedding [Finite D] {n : ℕ} (v : Selection n) (P : Subgroup D → Prop)
    (R : Subgroup (Original (D := D) n) → Prop) :
    SelectedFamily v P R ↪ CoverFamily n P where
  toFun H := ⟨lift v H.val.val, lift_full v H.val.val H.property,
    fun j => by rw [retained_image]; exact H.val.property.1 _, by
      rw [exterior_image]; exact H.val.property.2.1⟩
  inj' := by
    intro H K h
    have he := congrArg (fun L : CoverFamily n P => L.val.map (productMap v)) h
    change (lift v H.val.val).map (productMap v) =
      (lift v K.val.val).map (productMap v) at he
    exact Subtype.ext (Subtype.ext (by simpa only [reconstruct] using he))

theorem selectedEmbedding_reconstruct [Finite D] {n : ℕ} (v : Selection n)
    (P : Subgroup D → Prop) (R : Subgroup (Original (D := D) n) → Prop)
    (H : SelectedFamily v P R) :
    (selectedEmbedding v P R H).val.map (productMap v) = H.val.val := reconstruct v H.val.val

theorem reconstructed_predicate [Finite D] {n : ℕ} (v : Selection n)
    (P : Subgroup D → Prop) (R : Subgroup (Original (D := D) n) → Prop)
    (H : SelectedFamily v P R) :
    R ((selectedEmbedding v P R H).val.map (productMap v)) := by
  rw [selectedEmbedding_reconstruct]
  exact H.val.property.2.2

abbrev Incidence (n : ℕ) (P : Subgroup D → Prop)
    (R : Subgroup (Original (D := D) n) → Prop) :=
  Σ H : OriginalFamily n P R, {v : Selection n // Independent v H.val}

def incidenceEmbedding [Finite D] (n : ℕ) (P : Subgroup D → Prop)
    (R : Subgroup (Original (D := D) n) → Prop) :
    Incidence n P R ↪ Selection n × CoverFamily n P where
  toFun z := (z.2.val, selectedEmbedding z.2.val P R ⟨z.1, z.2.property⟩)
  inj' := by
    rintro ⟨H, v, hv⟩ ⟨K, w, hw⟩ he
    have h : v = w := congrArg Prod.fst he
    subst w
    have hK := (selectedEmbedding v P R).injective (congrArg Prod.snd he)
    have hHK : H = K := congrArg Subtype.val hK
    subst K
    rfl

local instance coveredSubgroupFinite [Finite D] (n : ℕ) :
    Finite (Subgroup (Covered (D := D) n)) :=
  Finite.of_injective (fun K : Subgroup (Covered (D := D) n) => (K : Set (Covered (D := D) n)))
    SetLike.coe_injective

/-- An actual incidence bound from the reconstruction injection, with no
joint-fullness or count premise. The selected four positions are ordered. -/
theorem incidence_card_le [Finite D] (n : ℕ) (P : Subgroup D → Prop)
    (R : Subgroup (Original (D := D) n) → Prop) :
    Nat.card (Incidence n P R) ≤
      (n + 4).descFactorial 4 * Nat.card (CoverFamily n P) := by
  have h := Nat.card_le_card_of_injective (incidenceEmbedding n P R)
    (incidenceEmbedding n P R).injective
  simpa only [Nat.card_prod, selection_card] using h

end SymmetricSubgroupAsymptotics.BinaryFourPairSelectedModel
