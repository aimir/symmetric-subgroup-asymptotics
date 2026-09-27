import SymmetricSubgroupAsymptotics.RepeatedCharacterPartition
import Mathlib.Data.Fintype.Card

/-!
# A presentation cover for original repeated-character images

Every original subgroup has a presentation on a finite retained coordinate
set, together with a surjective allocation of the original coordinates.
Expansion reconstructs that subgroup exactly. Choosing one presentation
therefore gives an injection into all presentations; no division by the
number of label enumerations is used. In particular, this module does not
claim that all presentations expand injectively.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.RepeatedCharacterPresentations

open RepeatedCharacterCollapse RepeatedCharacterPartition

variable {ι Q R C D : Type*} [Group C] [Group D]

def coordinateEquiv (e : Q ≃ R) : ((Q → C) × D) ≃* ((R → C) × D) where
  toFun y := (fun r => y.1 (e.symm r), y.2)
  invFun y := (fun q => y.1 (e q), y.2)
  left_inv y := by
    apply Prod.ext
    · funext q
      exact congrArg y.1 (e.symm_apply_apply q)
    · rfl
  right_inv y := by
    apply Prod.ext
    · funext r
      exact congrArg y.1 (e.apply_symm_apply r)
    · rfl
  map_mul' _ _ := rfl

def allocationExpand (f : ι → Q) : ((Q → C) × D) →* ((ι → C) × D) where
  toFun y := (fun i => y.1 (f i), y.2)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem allocationExpand_injective (f : ι → Q) (hf : Function.Surjective f) :
    Function.Injective (allocationExpand (C := C) (D := D) f) := by
  intro x y h
  apply Prod.ext
  · funext q
    obtain ⟨i, rfl⟩ := hf q
    exact congrArg (fun z : (ι → C) × D => z.1 i) h
  · exact congrArg (fun z : (ι → C) × D => z.2) h

def allocationExpanded (f : ι → Q) (Y : Subgroup ((Q → C) × D)) :
    Subgroup ((ι → C) × D) := Y.map (allocationExpand f)

def allocationEquiv (f : ι → Q) (hf : Function.Surjective f)
    (Y : Subgroup ((Q → C) × D)) : Y ≃* allocationExpanded f Y :=
  Subgroup.equivMapOfInjective Y (allocationExpand f) (allocationExpand_injective f hf)

@[simp] theorem character_allocation_comp (f : ι → Q) (hf : Function.Surjective f)
    (Y : Subgroup ((Q → C) × D)) (i : ι) :
    (character (allocationExpanded f Y) i).comp (allocationEquiv f hf Y).toMonoidHom =
      character Y (f i) := rfl

theorem allocation_exterior (f : ι → Q) (Y : Subgroup ((Q → C) × D)) :
    (allocationExpanded f Y).map (MonoidHom.snd (ι → C) D) =
      Y.map (MonoidHom.snd (Q → C) D) := by
  rw [allocationExpanded, Subgroup.map_map]
  rfl

theorem allocation_character_eq_one_iff (f : ι → Q) (hf : Function.Surjective f)
    (Y : Subgroup ((Q → C) × D)) (i : ι) :
    character (allocationExpanded f Y) i = 1 ↔ character Y (f i) = 1 := by
  constructor
  · intro h
    apply MonoidHom.ext
    intro y
    exact congrArg (fun a : allocationExpanded f Y →* C => a (allocationEquiv f hf Y y)) h
  · intro h
    apply MonoidHom.ext
    intro y
    obtain ⟨x, rfl⟩ := (allocationEquiv f hf Y).surjective y
    exact congrArg (fun a : Y →* C => a x) h

theorem allocation_characters_nontrivial_iff (f : ι → Q) (hf : Function.Surjective f)
    (Y : Subgroup ((Q → C) × D)) :
    (∀ i, character (allocationExpanded f Y) i ≠ 1) ↔
      (∀ q, character Y q ≠ 1) := by
  constructor
  · intro h q
    obtain ⟨i, rfl⟩ := hf q
    exact fun hi => h i ((allocation_character_eq_one_iff f hf Y i).mpr hi)
  · intro h i hi
    exact h (f i) ((allocation_character_eq_one_iff f hf Y i).mp hi)

theorem allocation_character_surjective_iff (f : ι → Q) (hf : Function.Surjective f)
    (Y : Subgroup ((Q → C) × D)) (i : ι) :
    Function.Surjective (character (allocationExpanded f Y) i) ↔
      Function.Surjective (character Y (f i)) := by
  constructor
  · intro h c
    obtain ⟨y, hy⟩ := h c
    obtain ⟨x, rfl⟩ := (allocationEquiv f hf Y).surjective y
    exact ⟨x, hy⟩
  · intro h c
    obtain ⟨x, hx⟩ := h c
    exact ⟨allocationEquiv f hf Y x, hx⟩

theorem allocation_characters_surjective_iff (f : ι → Q) (hf : Function.Surjective f)
    (Y : Subgroup ((Q → C) × D)) :
    (∀ i, Function.Surjective (character (allocationExpanded f Y) i)) ↔
      (∀ q, Function.Surjective (character Y q)) := by
  constructor
  · intro h q
    obtain ⟨i, rfl⟩ := hf q
    exact (allocation_character_surjective_iff f hf Y i).mp (h i)
  · intro h i
    exact (allocation_character_surjective_iff f hf Y i).mpr (h (f i))

theorem allocation_isPGroup_iff (f : ι → Q) (hf : Function.Surjective f)
    (Y : Subgroup ((Q → C) × D)) (p : ℕ) :
    IsPGroup p (allocationExpanded f Y) ↔ IsPGroup p Y :=
  ⟨fun h => h.of_equiv (allocationEquiv f hf Y).symm,
    fun h => h.of_equiv (allocationEquiv f hf Y)⟩

theorem allocationExpanded_reindexed (r : Setoid ι) (e : Quotient r ≃ Q)
    (Y : Subgroup ((Quotient r → C) × D)) :
    allocationExpanded (fun i => e (Quotient.mk r i))
      (Y.map (coordinateEquiv (C := C) (D := D) e).toMonoidHom) = expanded r Y := by
  change (Y.map (coordinateEquiv e).toMonoidHom).map
    (allocationExpand (fun i => e (Quotient.mk r i))) = Y.map (expand r)
  rw [Subgroup.map_map]
  apply congrArg (fun a => Y.map a)
  apply MonoidHom.ext
  intro y
  apply Prod.ext
  · funext i
    exact congrArg y.1 (e.symm_apply_apply (Quotient.mk r i))
  · rfl

section FiniteCoordinates

variable [Fintype ι]

def Presentation :=
  Σ q : Fin (Fintype.card ι + 1),
    {f : ι → Fin q.1 // Function.Surjective f} × Subgroup ((Fin q.1 → C) × D)

def original (z : Presentation (ι := ι) (C := C) (D := D)) :
    Subgroup ((ι → C) × D) := allocationExpanded z.2.1.1 z.2.2

theorem quotient_card_le (r : Setoid ι) : Fintype.card (Quotient r) ≤ Fintype.card ι :=
  Fintype.card_le_of_surjective (Quotient.mk r) (by
    intro q
    refine Quotient.inductionOn q ?_
    intro i
    exact ⟨i, rfl⟩)

/-- Choose an enumeration only to exhibit one member of the larger cover.
The exact inverse always reconstructs the same original subgroup. -/
def present (B : Subgroup ((ι → C) × D)) :
    Presentation (ι := ι) (C := C) (D := D) :=
  let r := relation B
  let e := Fintype.equivFin (Quotient r)
  ⟨⟨Fintype.card (Quotient r), Nat.lt_succ_of_le (quotient_card_le r)⟩,
    ⟨fun i => e (Quotient.mk r i), by
      intro q
      obtain ⟨a, rfl⟩ := e.surjective q
      refine Quotient.inductionOn a ?_
      intro i
      exact ⟨i, rfl⟩⟩,
    (collapsed B).map (coordinateEquiv e).toMonoidHom⟩

@[simp] theorem original_present (B : Subgroup ((ι → C) × D)) :
    original (present B) = B :=
  (allocationExpanded_reindexed (relation B) (Fintype.equivFin (Quotient (relation B)))
    (collapsed B)).trans (expanded_collapsed B)

theorem present_injective :
    Function.Injective (present (ι := ι) (C := C) (D := D)) := by
  intro B B' h
  simpa only [original_present] using congrArg original h

/-- Arbitrary original predicates can be carried into the presentation
cover. Dropping such a predicate later is an inclusion, not an equality. -/
def restrictedEmbedding (P : Subgroup ((ι → C) × D) → Prop) :
    {B // P B} ↪ {z : Presentation (ι := ι) (C := C) (D := D) // P (original z)} where
  toFun B := ⟨present B.1, by simpa only [original_present] using B.2⟩
  inj' _ _ h := Subtype.ext (present_injective (congrArg Subtype.val h))

instance presentationFinite [Finite C] [Finite D] :
    Finite (Presentation (ι := ι) (C := C) (D := D)) := by
  letI : ∀ q : Fin (Fintype.card ι + 1),
      Finite {f : ι → Fin q.1 // Function.Surjective f} := fun q =>
    Finite.of_injective
      (fun f : {f : ι → Fin q.1 // Function.Surjective f} => f.1) Subtype.val_injective
  letI : ∀ q : Fin (Fintype.card ι + 1),
      Finite (Subgroup ((Fin q.1 → C) × D)) := fun q =>
    Finite.of_injective
      (fun Y : Subgroup ((Fin q.1 → C) × D) => (Y : Set ((Fin q.1 → C) × D)))
      SetLike.coe_injective
  unfold Presentation
  infer_instance

theorem card_original_le_presentations [Finite C] [Finite D]
    (P : Subgroup ((ι → C) × D) → Prop) :
    Nat.card {B // P B} ≤
      Nat.card {z : Presentation (ι := ι) (C := C) (D := D) // P (original z)} := by
  exact Nat.card_le_card_of_injective (restrictedEmbedding P) (restrictedEmbedding P).injective

end FiniteCoordinates

end SymmetricSubgroupAsymptotics.RepeatedCharacterPresentations

end
