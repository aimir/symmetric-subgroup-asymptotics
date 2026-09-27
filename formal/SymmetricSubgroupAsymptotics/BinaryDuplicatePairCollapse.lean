import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Prod
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Literal collapse of two equal original pair characters

The pair action is the original permutation group on Fin 2. Equality means
equality of the two homomorphisms on the same subgroup. Collapse and expansion
are inverse on actual subgroups, retain the complete exterior image, and
therefore retain any predicate on that image. No independence, splitting,
finite exterior, or counting estimate is assumed. Physical orbit pointing
and its occurrence-factorial incidence are separate from this equivalence.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryDuplicatePairCollapse

abbrev Pair := Equiv.Perm (Fin 2)

variable {D : Type*} [Group D]

abbrev Original (D : Type*) := (Pair × Pair) × D
abbrev Collapsed (D : Type*) := Pair × D

def first : Original D →* Pair :=
  (MonoidHom.fst Pair Pair).comp (MonoidHom.fst (Pair × Pair) D)

def second : Original D →* Pair :=
  (MonoidHom.snd Pair Pair).comp (MonoidHom.fst (Pair × Pair) D)

def collapse : Original D →* Collapsed D where
  toFun x := (x.1.1, x.2)
  map_one' := rfl
  map_mul' _ _ := rfl

def expand : Collapsed D →* Original D where
  toFun x := ((x.1, x.1), x.2)
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem collapse_expand (x : Collapsed D) : collapse (expand x) = x := rfl

theorem expand_injective : Function.Injective (expand (D := D)) := by
  intro x y h
  exact congrArg collapse h

/-- The two actual characters of one original subgroup, with their source
and target unchanged. -/
def EqualCharacters (H : Subgroup (Original D)) : Prop :=
  first.comp H.subtype = second.comp H.subtype

theorem equalCharacters_iff (H : Subgroup (Original D)) :
    EqualCharacters H ↔ ∀ x ∈ H, x.1.1 = x.1.2 := by
  constructor
  · intro h x hx
    exact congrArg (fun f : H →* Pair => f ⟨x, hx⟩) h
  · intro h
    apply MonoidHom.ext
    intro x
    exact h x.val x.property

theorem expand_collapse (H : Subgroup (Original D)) (hH : EqualCharacters H)
    (x : Original D) (hx : x ∈ H) : expand (collapse x) = x := by
  apply Prod.ext
  · exact Prod.ext rfl ((equalCharacters_iff H).mp hH x hx)
  · rfl

theorem expand_map_equal (K : Subgroup (Collapsed D)) :
    EqualCharacters (K.map expand) := by
  rw [equalCharacters_iff]
  rintro x ⟨y, hy, rfl⟩
  rfl

theorem map_collapse_expand (H : Subgroup (Original D)) (hH : EqualCharacters H) :
    (H.map collapse).map expand = H := by
  apply le_antisymm
  · rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa only [expand_collapse H hH z hz] using hz
  · intro x hx
    exact ⟨collapse x, ⟨x, hx, rfl⟩, expand_collapse H hH x hx⟩

theorem map_expand_collapse (K : Subgroup (Collapsed D)) :
    (K.map expand).map collapse = K := by
  rw [Subgroup.map_map]
  change K.map (MonoidHom.id (Collapsed D)) = K
  exact Subgroup.map_id K

theorem collapse_exterior (H : Subgroup (Original D)) :
    (H.map collapse).map (MonoidHom.snd Pair D) =
      H.map (MonoidHom.snd (Pair × Pair) D) := by
  rw [Subgroup.map_map]
  rfl

theorem expand_exterior (K : Subgroup (Collapsed D)) :
    (K.map expand).map (MonoidHom.snd (Pair × Pair) D) =
      K.map (MonoidHom.snd Pair D) := by
  rw [Subgroup.map_map]
  rfl

abbrev OriginalFamily (P : Subgroup D → Prop) :=
  {H : Subgroup (Original D) // H.map first = ⊤ ∧ H.map second = ⊤ ∧
    EqualCharacters H ∧ P (H.map (MonoidHom.snd (Pair × Pair) D))}

abbrev CollapsedFamily (P : Subgroup D → Prop) :=
  {K : Subgroup (Collapsed D) // K.map (MonoidHom.fst Pair D) = ⊤ ∧
    P (K.map (MonoidHom.snd Pair D))}

/-- Both original pair coordinates are full, and every original exterior
condition survives verbatim. Expansion restores the original subgroup. -/
def familyEquiv (P : Subgroup D → Prop) : OriginalFamily P ≃ CollapsedFamily P where
  toFun H := ⟨H.val.map collapse, by
    constructor
    · rw [Subgroup.map_map]
      exact H.property.1
    · rw [collapse_exterior]
      exact H.property.2.2.2⟩
  invFun K := ⟨K.val.map expand, by
    refine ⟨?_, ?_, expand_map_equal K.val, ?_⟩
    · rw [Subgroup.map_map]
      exact K.property.1
    · rw [Subgroup.map_map]
      exact K.property.1
    · rw [expand_exterior]
      exact K.property.2⟩
  left_inv H := Subtype.ext (map_collapse_expand H.val H.property.2.2.1)
  right_inv K := Subtype.ext (map_expand_collapse K.val)

@[simp] theorem familyEquiv_original (P : Subgroup D → Prop) (H : OriginalFamily P) :
    ((familyEquiv P) H).val.map expand = H.val :=
  map_collapse_expand H.val H.property.2.2.1

@[simp] theorem familyEquiv_exterior (P : Subgroup D → Prop) (H : OriginalFamily P) :
    ((familyEquiv P) H).val.map (MonoidHom.snd Pair D) =
      H.val.map (MonoidHom.snd (Pair × Pair) D) := collapse_exterior H.val

/-- Exact original subgroup count, with no estimate on the exterior family. -/
theorem family_card (P : Subgroup D → Prop) :
    Nat.card (OriginalFamily P) = Nat.card (CollapsedFamily P) :=
  Nat.card_congr (familyEquiv P)

end SymmetricSubgroupAsymptotics.BinaryDuplicatePairCollapse
