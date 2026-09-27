import SymmetricSubgroupAsymptotics.RepeatedCharacterCollapse
import Mathlib.Data.Setoid.Basic

/-!
# Canonical partitions for repeated original coordinate characters

A subgroup of `C^ι × D` determines the equality relation of its actual
coordinate homomorphisms. Its quotient coordinates carry a subgroup with
distinct coordinate homomorphisms, and expansion reconstructs the original
subgroup exactly. This is an equivalence of actual subgroup parameters,
without choosing an ordering of the distinct characters.

The exterior coordinate is retained verbatim. In particular, this result
does not identify presentations on an independently labelled smaller product,
nor assert a physical counting formula for those presentations.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.RepeatedCharacterPartition

open RepeatedCharacterCollapse

variable {ι C D : Type*} [Group C] [Group D]

/-- Equality of the homomorphisms on the same original subgroup. -/
def relation (B : Subgroup ((ι → C) × D)) : Setoid ι :=
  Setoid.ker (character B)

/-- Restore each original coordinate from its literal quotient class. -/
def expand (r : Setoid ι) : ((Quotient r → C) × D) →* ((ι → C) × D) where
  toFun y := (fun i => y.1 (Quotient.mk r i), y.2)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem expand_injective (r : Setoid ι) :
    Function.Injective (expand (C := C) (D := D) r) := by
  intro x y h
  apply Prod.ext
  · funext q
    refine Quotient.inductionOn q ?_
    intro i
    exact congrArg (fun z : (ι → C) × D => z.1 i) h
  · exact congrArg (fun z : (ι → C) × D => z.2) h

def expanded (r : Setoid ι) (Y : Subgroup ((Quotient r → C) × D)) :
    Subgroup ((ι → C) × D) :=
  Y.map (expand r)

def expansionEquiv (r : Setoid ι) (Y : Subgroup ((Quotient r → C) × D)) :
    Y ≃* expanded r Y :=
  Subgroup.equivMapOfInjective Y (expand r) (expand_injective r)

@[simp] theorem expansionEquiv_coe (r : Setoid ι)
    (Y : Subgroup ((Quotient r → C) × D)) (y : Y) :
    (expansionEquiv r Y y : (ι → C) × D) = expand r y.1 := rfl

@[simp] theorem character_expansion_comp (r : Setoid ι)
    (Y : Subgroup ((Quotient r → C) × D)) (i : ι) :
    (character (expanded r Y) i).comp (expansionEquiv r Y).toMonoidHom =
      character Y (Quotient.mk r i) := rfl

def quotientCharacter (B : Subgroup ((ι → C) × D)) :
    Quotient (relation B) → (B →* C) :=
  Setoid.kerLift (character B)

theorem quotientCharacter_injective (B : Subgroup ((ι → C) × D)) :
    Function.Injective (quotientCharacter B) :=
  Setoid.kerLift_injective (character B)

def collapse (B : Subgroup ((ι → C) × D)) :
    B →* ((Quotient (relation B) → C) × D) where
  toFun b := (fun q => quotientCharacter B q b, b.1.2)
  map_one' := by
    apply Prod.ext
    · funext q
      exact (quotientCharacter B q).map_one
    · rfl
  map_mul' b c := by
    apply Prod.ext
    · funext q
      exact (quotientCharacter B q).map_mul b c
    · rfl

@[simp] theorem expand_collapse (B : Subgroup ((ι → C) × D)) (b : B) :
    expand (relation B) (collapse B b) = b.1 := rfl

theorem collapse_injective (B : Subgroup ((ι → C) × D)) :
    Function.Injective (collapse B) := by
  intro b c h
  exact Subtype.ext (congrArg (expand (relation B)) h)

def collapsed (B : Subgroup ((ι → C) × D)) :
    Subgroup ((Quotient (relation B) → C) × D) :=
  (collapse B).range

def collapseToImage (B : Subgroup ((ι → C) × D)) : B →* collapsed B :=
  (collapse B).codRestrict (collapsed B) (fun b => ⟨b, rfl⟩)

theorem collapseToImage_surjective (B : Subgroup ((ι → C) × D)) :
    Function.Surjective (collapseToImage B) := by
  rintro ⟨y, b, rfl⟩
  exact ⟨b, rfl⟩

def collapseEquiv (B : Subgroup ((ι → C) × D)) : B ≃* collapsed B :=
  MulEquiv.ofBijective (collapseToImage B)
    ⟨fun _ _ h => collapse_injective B (congrArg Subtype.val h),
      collapseToImage_surjective B⟩

@[simp] theorem collapsed_character_comp (B : Subgroup ((ι → C) × D))
    (q : Quotient (relation B)) :
    (character (collapsed B) q).comp (collapseToImage B) =
      quotientCharacter B q := rfl

theorem collapsed_characters_distinct (B : Subgroup ((ι → C) × D)) :
    Function.Injective (character (collapsed B)) := by
  intro q q' h
  apply quotientCharacter_injective B
  exact congrArg (fun f => f.comp (collapseToImage B)) h

theorem expanded_collapsed (B : Subgroup ((ι → C) × D)) :
    expanded (relation B) (collapsed B) = B := by
  apply le_antisymm
  · rintro _ ⟨y, ⟨b, rfl⟩, rfl⟩
    exact b.2
  · intro b hb
    exact ⟨collapse B ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩, rfl⟩

/-- Distinct coordinates on the smaller actual image recover precisely the
original partition after expansion. -/
theorem relation_expanded (r : Setoid ι)
    (Y : Subgroup ((Quotient r → C) × D))
    (hY : Function.Injective (character Y)) :
    relation (expanded r Y) = r := by
  apply Setoid.ext
  intro i j
  change character (expanded r Y) i = character (expanded r Y) j ↔ r i j
  constructor
  · intro h
    apply Quotient.exact
    apply hY
    exact congrArg (fun f => f.comp (expansionEquiv r Y).toMonoidHom) h
  · intro h
    apply MonoidHom.ext
    intro b
    obtain ⟨y, rfl⟩ := (expansionEquiv r Y).surjective b
    change y.1.1 (Quotient.mk r i) = y.1.1 (Quotient.mk r j)
    exact congrArg y.1.1 (Quotient.sound h)

/-- The retained product is indexed by quotient classes, not by an arbitrary
ordering of the retained homomorphisms. -/
def CollapsedData (r : Setoid ι) :=
  {Y : Subgroup ((Quotient r → C) × D) // Function.Injective (character Y)}

def Data := Σ r : Setoid ι, CollapsedData (C := C) (D := D) r

def encode (B : Subgroup ((ι → C) × D)) : Data (ι := ι) (C := C) (D := D) :=
  ⟨relation B, collapsed B, collapsed_characters_distinct B⟩

def decode (z : Data (ι := ι) (C := C) (D := D)) : Subgroup ((ι → C) × D) :=
  expanded z.1 z.2.1

@[simp] theorem decode_encode (B : Subgroup ((ι → C) × D)) :
    decode (encode B) = B := expanded_collapsed B

@[simp] theorem relation_decode (z : Data (ι := ι) (C := C) (D := D)) :
    relation (decode z) = z.1 :=
  relation_expanded z.1 z.2.1 z.2.2

theorem decode_injective :
    Function.Injective (decode (ι := ι) (C := C) (D := D)) := by
  rintro ⟨r, Y, hY⟩ ⟨s, Z, hZ⟩ h
  have hrs : r = s := by
    simpa only [relation_decode] using congrArg relation h
  subst s
  have hYZ : Y = Z := Subgroup.map_injective (expand_injective r) h
  subst Z
  rfl

/-- Exact reversible collapse of every original subgroup, with no extra
label-ordering parameter or exterior replacement. -/
def equiv : Subgroup ((ι → C) × D) ≃ Data (ι := ι) (C := C) (D := D) where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv z := decode_injective (decode_encode (decode z))

/-- A predicate on the original subgroup is retained by reconstruction,
without assuming that it is constant on an auxiliary presentation. -/
def restrictedEquiv (P : Subgroup ((ι → C) × D) → Prop) :
    {B // P B} ≃ {z : Data (ι := ι) (C := C) (D := D) // P (decode z)} where
  toFun B := ⟨encode B.1, by simpa only [decode_encode] using B.2⟩
  invFun z := ⟨decode z.1, z.2⟩
  left_inv B := Subtype.ext (decode_encode B.1)
  right_inv z := Subtype.ext ((equiv (ι := ι) (C := C) (D := D)).apply_symm_apply z.1)

/-- The canonical quotient classes are exactly the existing actual character
labels, so their multiplicities remain tied to the original coordinates. -/
def labelEquiv (B : Subgroup ((ι → C) × D)) :
    Quotient (relation B) ≃ RepeatedCharacterCollapse.Label B :=
  Setoid.quotientKerEquivRange (character B)

@[simp] theorem labelEquiv_mk (B : Subgroup ((ι → C) × D)) (i : ι) :
    labelEquiv B (Quotient.mk (relation B) i) =
      RepeatedCharacterCollapse.label B i := by
  apply Subtype.ext
  rfl

theorem expanded_exterior (r : Setoid ι)
    (Y : Subgroup ((Quotient r → C) × D)) :
    (expanded r Y).map (MonoidHom.snd (ι → C) D) =
      Y.map (MonoidHom.snd (Quotient r → C) D) := by
  rw [expanded, Subgroup.map_map]
  rfl

theorem collapsed_isPGroup (B : Subgroup ((ι → C) × D)) {p : ℕ}
    (hB : IsPGroup p B) : IsPGroup p (collapsed B) :=
  hB.of_equiv (collapseEquiv B)

theorem expanded_isPGroup (r : Setoid ι)
    (Y : Subgroup ((Quotient r → C) × D)) {p : ℕ}
    (hY : IsPGroup p Y) : IsPGroup p (expanded r Y) :=
  hY.of_equiv (expansionEquiv r Y)

theorem expanded_isPGroup_iff (r : Setoid ι)
    (Y : Subgroup ((Quotient r → C) × D)) (p : ℕ) :
    IsPGroup p (expanded r Y) ↔ IsPGroup p Y :=
  ⟨fun h => h.of_equiv (expansionEquiv r Y).symm, expanded_isPGroup r Y⟩

theorem expanded_character_eq_one_iff (r : Setoid ι)
    (Y : Subgroup ((Quotient r → C) × D)) (i : ι) :
    character (expanded r Y) i = 1 ↔ character Y (Quotient.mk r i) = 1 := by
  constructor
  · intro h
    apply MonoidHom.ext
    intro y
    exact congrArg (fun f : expanded r Y →* C => f (expansionEquiv r Y y)) h
  · intro h
    apply MonoidHom.ext
    intro b
    obtain ⟨y, rfl⟩ := (expansionEquiv r Y).surjective b
    exact congrArg (fun f : Y →* C => f y) h

theorem expanded_characters_nontrivial_iff (r : Setoid ι)
    (Y : Subgroup ((Quotient r → C) × D)) :
    (∀ i, character (expanded r Y) i ≠ 1) ↔
      (∀ q, character Y q ≠ 1) := by
  constructor
  · intro h q
    refine Quotient.inductionOn q ?_
    intro i
    exact fun hi => h i ((expanded_character_eq_one_iff r Y i).mpr hi)
  · intro h i hi
    exact h (Quotient.mk r i) ((expanded_character_eq_one_iff r Y i).mp hi)

theorem expanded_character_surjective_iff (r : Setoid ι)
    (Y : Subgroup ((Quotient r → C) × D)) (i : ι) :
    Function.Surjective (character (expanded r Y) i) ↔
      Function.Surjective (character Y (Quotient.mk r i)) := by
  constructor
  · intro h c
    obtain ⟨b, hb⟩ := h c
    obtain ⟨y, rfl⟩ := (expansionEquiv r Y).surjective b
    exact ⟨y, hb⟩
  · intro h c
    obtain ⟨y, hy⟩ := h c
    exact ⟨expansionEquiv r Y y, hy⟩

theorem expanded_characters_surjective_iff (r : Setoid ι)
    (Y : Subgroup ((Quotient r → C) × D)) :
    (∀ i, Function.Surjective (character (expanded r Y) i)) ↔
      (∀ q, Function.Surjective (character Y q)) := by
  constructor
  · intro h q
    refine Quotient.inductionOn q ?_
    intro i
    exact (expanded_character_surjective_iff r Y i).mp (h i)
  · intro h i
    exact (expanded_character_surjective_iff r Y i).mpr (h (Quotient.mk r i))

/-- The actual repeated-character fibres are the quotient allocation fibres.
This equivalence keeps each original coordinate fixed. -/
def coordinateFibreEquiv (B : Subgroup ((ι → C) × D))
    (q : Quotient (relation B)) :
    {i : ι // Quotient.mk (relation B) i = q} ≃
      {i : ι // RepeatedCharacterCollapse.label B i = labelEquiv B q} where
  toFun i := ⟨i.1, by rw [← labelEquiv_mk, i.2]⟩
  invFun i := ⟨i.1, (labelEquiv B).injective (by simpa only [labelEquiv_mk] using i.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

end SymmetricSubgroupAsymptotics.RepeatedCharacterPartition

end
