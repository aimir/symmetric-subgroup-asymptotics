import SymmetricSubgroupAsymptotics.RepeatedCharacterFixedAllocation
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.Perm.Basic

/-!
# All selected duplicate pairs in the original full-coordinate model

For each actual unordered two-element subset of the original positions,
collapse exactly those positions. No ordering of the chosen pair is added.
The resulting exact incidence counts all original equal-character pairs,
including further coincidences, and keeps every exterior-image condition.
This model incidence does not yet assert physical orbit-profile assembly.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.BinaryDuplicatePairModelCount

open RepeatedCharacterCollapse RepeatedCharacterFixedAllocation

variable {C D : Type*} [Group C] [Group D]

/-- Full-coordinate families depend only on the coordinate set through an
actual reindexing; the complete original exterior is untouched. -/
def familyReindex {I Q : Type*} (e : I ≃ Q) (P : Subgroup D → Prop) :
    Family (C := C) I P ≃ Family (C := C) Q P :=
  let lift : Family (C := C) I P ≃ OriginalFamily (C := C) e P :=
   { toFun := fun H => ⟨H, by
      intro i j hij
      rw [e.injective hij]⟩
     invFun := fun H => H.val
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl }
  lift.trans (familyEquiv e e.surjective P)

abbrev Selection (n : ℕ) := {s : Finset (Fin (n + 2)) // s.card = 2}

abbrev Remaining {n : ℕ} (s : Selection n) := {i : Fin (n + 2) // i ∉ s.val}
abbrev Retained {n : ℕ} (s : Selection n) := Option (Remaining s)

/-- None is the one collapsed pair; every other original position retains
its own literal label. -/
def allocation {n : ℕ} (s : Selection n) (i : Fin (n + 2)) : Retained s :=
  if hi : i ∈ s.val then none else some ⟨i, hi⟩

theorem allocation_surjective {n : ℕ} (s : Selection n) :
    Function.Surjective (allocation s) := by
  intro q
  cases q with
  | none =>
      have hs : s.val.Nonempty := Finset.card_pos.mp (by rw [s.property]; decide)
      obtain ⟨i, hi⟩ := hs
      exact ⟨i, by simp [allocation, hi]⟩
  | some i => exact ⟨i.val, by simp [allocation, i.property]⟩

theorem remaining_card {n : ℕ} (s : Selection n) : Fintype.card (Remaining s) = n := by
  change Fintype.card {i : Fin (n + 2) // i ∉ s.val} = n
  rw [Fintype.card_subtype_compl]
  have hs : Fintype.card {i : Fin (n + 2) // i ∈ s.val} = 2 :=
    (Fintype.card_coe s.val).trans s.property
  rw [Fintype.card_fin, hs]
  omega

theorem retained_card {n : ℕ} (s : Selection n) : Fintype.card (Retained s) = n + 1 := by
  change Fintype.card (Option (Remaining s)) = n + 1
  rw [Fintype.card_option, remaining_card]

def retainedEquiv {n : ℕ} (s : Selection n) : Retained s ≃ Fin (n + 1) :=
  Fintype.equivFinOfCardEq (retained_card s)

/-- Equality is between homomorphisms on the same original subgroup. -/
def Duplicate {n : ℕ} (s : Selection n) (H : Subgroup ((Fin (n + 2) → C) × D)) : Prop :=
  ∀ i ∈ s.val, ∀ j ∈ s.val, character H i = character H j

theorem duplicate_iff_constant {n : ℕ} (s : Selection n)
    (H : Subgroup ((Fin (n + 2) → C) × D)) :
    Duplicate s H ↔ ConstantOnFibres (allocation s) H := by
  constructor
  · intro h i j hij
    by_cases hi : i ∈ s.val <;> by_cases hj : j ∈ s.val
    · exact h i hi j hj
    · simp [allocation, hi, hj] at hij
    · simp [allocation, hi, hj] at hij
    · have he : i = j := by simpa [allocation, hi, hj] using hij
      rw [he]
  · intro h i hi j hj
    exact h i j (by simp [allocation, hi, hj])

abbrev SelectedFamily {n : ℕ} (s : Selection n) (P : Subgroup D → Prop) :=
  {H : Family (C := C) (Fin (n + 2)) P // Duplicate s H.val}

/-- No cardinality premise is supplied: each selected-pair fibre is the
complete original family on one fewer coordinate. -/
def selectedFamilyEquiv {n : ℕ} (s : Selection n) (P : Subgroup D → Prop) :
    SelectedFamily (C := C) s P ≃ Family (C := C) (Fin (n + 1)) P :=
  let lift : SelectedFamily (C := C) s P ≃ OriginalFamily (C := C) (allocation s) P :=
   { toFun := fun H => ⟨H.val, (duplicate_iff_constant s H.val.val).mp H.property⟩
     invFun := fun H => ⟨H.val, (duplicate_iff_constant s H.val.val).mpr H.property⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl }
  (lift.trans
    (familyEquiv (allocation s) (allocation_surjective s) P)).trans
      (familyReindex (retainedEquiv s) P)

theorem selectedFamily_card {n : ℕ} (s : Selection n) (P : Subgroup D → Prop) :
    Nat.card (SelectedFamily (C := C) s P) = Nat.card (Family (C := C) (Fin (n + 1)) P) :=
  Nat.card_congr (selectedFamilyEquiv s P)

theorem selection_card (n : ℕ) : Nat.card (Selection n) = (n + 2).choose 2 := by
  let e : Selection n ≃ ((Finset.univ : Finset (Fin (n + 2))).powersetCard 2) :=
    { toFun := fun s => ⟨s.val, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, s.property⟩⟩
      invFun := fun s => ⟨s.val, (Finset.mem_powersetCard.mp s.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- The original subgroup is retained alongside its unordered selected pair. -/
abbrev Incidence (n : ℕ) (P : Subgroup D → Prop) :=
  Σ H : Family (C := C) (Fin (n + 2)) P, {s : Selection n // Duplicate s H.val}

def incidenceEquiv (n : ℕ) (P : Subgroup D → Prop) :
    Incidence (C := C) n P ≃ Σ s : Selection n, SelectedFamily (C := C) s P where
  toFun z := ⟨z.2.val, z.1, z.2.property⟩
  invFun z := ⟨z.2.val, z.1, z.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

section Finite

variable [Finite C] [Finite D]

local instance modelSubgroupFinite (J : Type*) [Finite J] :
    Finite (Subgroup ((J → C) × D)) :=
  Finite.of_injective (fun H : Subgroup ((J → C) × D) => (H : Set ((J → C) × D)))
    SetLike.coe_injective

/-- Exact complete incidence, with all repeated characters allowed in the
collapsed target. No factor from ordering the selected pair occurs. -/
theorem incidence_card (n : ℕ) (P : Subgroup D → Prop) :
    Nat.card (Incidence (C := C) n P) =
      (n + 2).choose 2 * Nat.card (Family (C := C) (Fin (n + 1)) P) := by
  rw [Nat.card_congr (incidenceEquiv n P), Nat.card_sigma]
  simp_rw [selectedFamily_card]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card, selection_card]
  simp

/-- Sum over the literal original subgroups of their numbers of unordered
equal-character pair selections. -/
theorem duplicate_sum (n : ℕ) (P : Subgroup D → Prop) :
    (∑ H : Family (C := C) (Fin (n + 2)) P,
      Nat.card {s : Selection n // Duplicate s H.val}) =
      (n + 2).choose 2 * Nat.card (Family (C := C) (Fin (n + 1)) P) := by
  rw [← Nat.card_sigma]
  exact incidence_card n P

end Finite

end SymmetricSubgroupAsymptotics.BinaryDuplicatePairModelCount
