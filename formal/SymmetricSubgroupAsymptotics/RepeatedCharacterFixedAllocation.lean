import SymmetricSubgroupAsymptotics.RepeatedCharacterPresentations

/-!
# Collapse only a specified collection of coordinate equalities

A fixed surjection of original positions prescribes which coordinate
characters must agree. Other coincidences are unrestricted. The complete
full-coordinate subgroup family satisfying these equalities is in exact
bijection with the smaller full-coordinate family. The original exterior
image, and every predicate on it, are preserved. In particular, this can
collapse one selected duplicate pair without deleting other duplicates.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.RepeatedCharacterFixedAllocation

open RepeatedCharacterCollapse RepeatedCharacterPresentations

variable {I Q C D : Type*} [Group C] [Group D]
    (f : I → Q) (hf : Function.Surjective f)

def ConstantOnFibres (H : Subgroup ((I → C) × D)) : Prop :=
  ∀ i j, f i = f j → character H i = character H j

include hf in
/-- The imposed equalities are exactly membership in the literal diagonal
range. They do not assert that different retained characters are distinct. -/
theorem constantOnFibres_iff_le_range (H : Subgroup ((I → C) × D)) :
    ConstantOnFibres f H ↔ H ≤ (allocationExpand (C := C) (D := D) f).range := by
  constructor
  · intro h x hx
    let y : (Q → C) × D := (fun q => x.1 (hf q).choose, x.2)
    refine ⟨y, ?_⟩
    apply Prod.ext
    · funext i
      change x.1 (hf (f i)).choose = x.1 i
      have he := h (hf (f i)).choose i (hf (f i)).choose_spec
      exact congrArg (fun a : H →* C => a ⟨x, hx⟩) he
    · rfl
  · intro h i j hij
    apply MonoidHom.ext
    intro x
    obtain ⟨y, hy⟩ := h x.property
    change x.val.1 i = x.val.1 j
    rw [← hy]
    change y.1 (f i) = y.1 (f j)
    rw [hij]

abbrev Family (J : Type*) (P : Subgroup D → Prop) :=
  {H : Subgroup ((J → C) × D) //
    (∀ i, Function.Surjective (character H i)) ∧
      P (H.map (MonoidHom.snd (J → C) D))}

abbrev OriginalFamily (P : Subgroup D → Prop) :=
  {H : Family (C := C) I P // ConstantOnFibres f H.val}

def contracted (H : Subgroup ((I → C) × D)) : Subgroup ((Q → C) × D) :=
  H.comap (allocationExpand f)

include hf in
theorem expanded_contracted (H : Subgroup ((I → C) × D))
    (hH : ConstantOnFibres f H) : allocationExpanded f (contracted f H) = H := by
  exact Subgroup.map_comap_eq_self ((constantOnFibres_iff_le_range f hf H).mp hH)

include hf in
theorem contracted_expanded (K : Subgroup ((Q → C) × D)) :
    contracted f (allocationExpanded f K) = K :=
  Subgroup.comap_map_eq_self_of_injective (allocationExpand_injective f hf) K

include hf in
theorem contracted_exterior (H : Subgroup ((I → C) × D))
    (hH : ConstantOnFibres f H) :
    (contracted f H).map (MonoidHom.snd (Q → C) D) =
      H.map (MonoidHom.snd (I → C) D) := by
  have h := allocation_exterior f (contracted f H)
  rw [expanded_contracted f hf H hH] at h
  exact h.symm

include hf in
theorem expanded_constant (K : Subgroup ((Q → C) × D)) :
    ConstantOnFibres f (allocationExpanded f K) := by
  apply (constantOnFibres_iff_le_range f hf _).mpr
  rintro x ⟨y, hy, rfl⟩
  exact ⟨y, rfl⟩

/-- Actual subgroup equivalence for this fixed allocation. All original
coordinate surjectivities and the complete original exterior are retained. -/
def familyEquiv (P : Subgroup D → Prop) :
    OriginalFamily (C := C) f P ≃ Family (C := C) Q P where
  toFun H := ⟨contracted f H.val.val, by
    constructor
    · apply (allocation_characters_surjective_iff f hf _).mp
      rw [expanded_contracted f hf H.val.val H.property]
      exact H.val.property.1
    · rw [contracted_exterior f hf H.val.val H.property]
      exact H.val.property.2⟩
  invFun K := ⟨⟨allocationExpanded f K.val, by
    constructor
    · exact (allocation_characters_surjective_iff f hf K.val).mpr K.property.1
    · rw [allocation_exterior]
      exact K.property.2⟩, expanded_constant f hf K.val⟩
  left_inv H := Subtype.ext (Subtype.ext (expanded_contracted f hf H.val.val H.property))
  right_inv K := Subtype.ext (contracted_expanded f hf K.val)

include hf in
theorem family_card (P : Subgroup D → Prop) :
    Nat.card (OriginalFamily (C := C) f P) = Nat.card (Family (C := C) Q P) :=
  Nat.card_congr (familyEquiv f hf P)

/-- The exact scalar equality on the whole exterior image is independent
of any original normalizer or later choice of physical labels. -/
theorem familyEquiv_exterior (P : Subgroup D → Prop) (H : OriginalFamily (C := C) f P) :
    ((familyEquiv f hf P) H).val.map (MonoidHom.snd (Q → C) D) =
      H.val.val.map (MonoidHom.snd (I → C) D) :=
  contracted_exterior f hf H.val.val H.property

end SymmetricSubgroupAsymptotics.RepeatedCharacterFixedAllocation
