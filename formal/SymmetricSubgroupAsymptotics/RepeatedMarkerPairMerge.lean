import SymmetricSubgroupAsymptotics.RepeatedCharacterPresentations
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Merge retained and preexisting pair coordinates

The first q coordinates and the preexisting p coordinates become one
coordinate family of size q+p. The exterior is unchanged, and fullness
is transported for every original coordinate. This is a literal group
and subgroup reindexing. It imposes no independence or distinctness on
coordinate characters and makes no separated-color assumption.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.RepeatedMarkerPairMerge

open RepeatedCharacterCollapse

variable {C D : Type*} [Group C] [Group D] (q p : ℕ)

abbrev Source := (Fin q → C) × ((Fin p → C) × D)
abbrev Target := (Fin (q+p) → C) × D

def merge : Source (C := C) (D := D) q p ≃* Target (C := C) (D := D) q p where
  toFun x := (Fin.addCases x.1 x.2.1, x.2.2)
  invFun y := (fun i => y.1 (Fin.castAdd p i), fun j => y.1 (Fin.natAdd q j), y.2)
  left_inv x := by
    apply Prod.ext
    · funext i
      simp
    · apply Prod.ext
      · funext j
        simp
      · rfl
  right_inv y := by
    apply Prod.ext
    · funext k
      refine Fin.addCases ?_ ?_ k
      · intro i
        simp
      · intro j
        simp
    · rfl
  map_mul' x y := by
    apply Prod.ext
    · funext k
      refine Fin.addCases ?_ ?_ k
      · intro i
        simp
      · intro j
        simp
    · rfl

@[simp] theorem merge_new (x : Source (C := C) (D := D) q p) (i : Fin q) :
    (merge q p x).1 (Fin.castAdd p i) = x.1 i := by
  change Fin.addCases x.1 x.2.1 (Fin.castAdd p i) = x.1 i
  simp

@[simp] theorem merge_old (x : Source (C := C) (D := D) q p) (j : Fin p) :
    (merge q p x).1 (Fin.natAdd q j) = x.2.1 j := by
  change Fin.addCases x.1 x.2.1 (Fin.natAdd q j) = x.2.1 j
  simp

@[simp] theorem merge_exterior (x : Source (C := C) (D := D) q p) :
    (merge q p x).2 = x.2.2 := rfl

def exterior : Source (C := C) (D := D) q p →* D :=
  (MonoidHom.snd (Fin p → C) D).comp (MonoidHom.snd (Fin q → C) _)

def merged (Y : Subgroup (Source (C := C) (D := D) q p)) :
    Subgroup (Target (C := C) (D := D) q p) := Y.map (merge q p).toMonoidHom

def subgroupEquiv (Y : Subgroup (Source (C := C) (D := D) q p)) :
    Y ≃* merged q p Y :=
  Subgroup.equivMapOfInjective Y (merge (C := C) (D := D) q p).toMonoidHom
    (merge (C := C) (D := D) q p).injective

@[simp] theorem subgroupEquiv_coe (Y : Subgroup (Source (C := C) (D := D) q p))
    (y : Y) : (subgroupEquiv q p Y y : Target (C := C) (D := D) q p) =
      merge q p y.1 := rfl

def oldCharacter (Y : Subgroup (Source (C := C) (D := D) q p)) (j : Fin p) :
    Y →* C where
  toFun y := y.1.2.1 j
  map_one' := rfl
  map_mul' _ _ := rfl

theorem character_new_comp (Y : Subgroup (Source (C := C) (D := D) q p))
    (i : Fin q) :
    (character (merged q p Y) (Fin.castAdd p i)).comp
      (subgroupEquiv q p Y).toMonoidHom = character Y i := by
  apply MonoidHom.ext
  intro y
  exact merge_new q p y.1 i

theorem character_old_comp (Y : Subgroup (Source (C := C) (D := D) q p))
    (j : Fin p) :
    (character (merged q p Y) (Fin.natAdd q j)).comp
      (subgroupEquiv q p Y).toMonoidHom = oldCharacter q p Y j := by
  apply MonoidHom.ext
  intro y
  exact merge_old q p y.1 j

/-- Fullness is retained on all q+p actual coordinates, even when the
two displayed blocks have the same permutation action type. -/
theorem merged_full_iff (Y : Subgroup (Source (C := C) (D := D) q p)) :
    (∀ k, Function.Surjective (character (merged q p Y) k)) ↔
      (∀ i, Function.Surjective (character Y i)) ∧
        (∀ j, Function.Surjective (oldCharacter q p Y j)) := by
  constructor
  · intro h
    constructor
    · intro i c
      obtain ⟨y, hy⟩ := h (Fin.castAdd p i) c
      obtain ⟨x, rfl⟩ := (subgroupEquiv q p Y).surjective y
      refine ⟨x, ?_⟩
      change (merge q p x.1).1 (Fin.castAdd p i) = c at hy
      rw [merge_new] at hy
      exact hy
    · intro j c
      obtain ⟨y, hy⟩ := h (Fin.natAdd q j) c
      obtain ⟨x, rfl⟩ := (subgroupEquiv q p Y).surjective y
      refine ⟨x, ?_⟩
      change (merge q p x.1).1 (Fin.natAdd q j) = c at hy
      rw [merge_old] at hy
      exact hy
  · rintro ⟨hn, ho⟩ k
    refine Fin.addCases ?_ ?_ k
    · intro i c
      obtain ⟨x, hx⟩ := hn i c
      refine ⟨subgroupEquiv q p Y x, ?_⟩
      change (merge q p x.1).1 (Fin.castAdd p i) = c
      rw [merge_new]
      exact hx
    · intro j c
      obtain ⟨x, hx⟩ := ho j c
      refine ⟨subgroupEquiv q p Y x, ?_⟩
      change (merge q p x.1).1 (Fin.natAdd q j) = c
      rw [merge_old]
      exact hx

theorem merged_exterior (Y : Subgroup (Source (C := C) (D := D) q p)) :
    (merged q p Y).map (MonoidHom.snd (Fin (q+p) → C) D) =
      Y.map (exterior q p) := by
  rw [merged, Subgroup.map_map]
  rfl

theorem merged_exterior_projection {E : Type*} [Group E] (f : D →* E)
    (Y : Subgroup (Source (C := C) (D := D) q p)) :
    (merged q p Y).map (f.comp (MonoidHom.snd (Fin (q+p) → C) D)) =
      Y.map (f.comp (exterior q p)) := by
  rw [← Subgroup.map_map, merged_exterior, Subgroup.map_map]

theorem merged_isPGroup_iff (Y : Subgroup (Source (C := C) (D := D) q p)) (r : ℕ) :
    IsPGroup r (merged q p Y) ↔ IsPGroup r Y :=
  ⟨fun h => h.of_equiv (subgroupEquiv q p Y).symm,
    fun h => h.of_equiv (subgroupEquiv q p Y)⟩

/-- Retain any original subgroup predicate by exact reconstruction. -/
def familyEquiv (P : Subgroup (Source (C := C) (D := D) q p) → Prop) :
    {Y // P Y} ≃
      {Z : Subgroup (Target (C := C) (D := D) q p) //
        P (Z.comap (merge q p).toMonoidHom)} where
  toFun Y := ⟨merged q p Y.1, by
    rw [merged, Subgroup.comap_map_eq_self_of_injective (merge q p).injective]
    exact Y.2⟩
  invFun Z := ⟨Z.1.comap (merge (C := C) (D := D) q p).toMonoidHom, Z.2⟩
  left_inv Y := Subtype.ext
    (Subgroup.comap_map_eq_self_of_injective
      (f := (merge (C := C) (D := D) q p).toMonoidHom)
      (merge (C := C) (D := D) q p).injective Y.1)
  right_inv Z := Subtype.ext
    (Subgroup.map_comap_eq_self_of_surjective
      (f := (merge (C := C) (D := D) q p).toMonoidHom)
      (merge (C := C) (D := D) q p).surjective Z.1)

end SymmetricSubgroupAsymptotics.RepeatedMarkerPairMerge

end
