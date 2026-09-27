import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sum
import Mathlib.SetTheory.Cardinal.Finite
import Lean.Elab.Tactic.Omega

/-!
# Distinct labels and actual duplicate pairs

For any finite family of labels, every occurrence after the first injects
into an unordered pair of equal labels. In particular the number of actual
pair orbits is at most the number of distinct characters plus the number
of actual unordered equal-character pairs. No linear independence or
distinctness of the remaining labels is assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.CharacterCollisionCount

variable {I A : Type*} (f : I → A)

/-- An unordered pair of distinct original occurrences carrying one label. -/
abbrev Collision :=
  {s : Finset I // s.card = 2 ∧ ∀ i ∈ s, ∀ j ∈ s, f i = f j}

def representative (a : Set.range f) : I := a.property.choose

@[simp] theorem representative_label (a : Set.range f) :
    f (representative f a) = a.val := a.property.choose_spec

def label (i : I) : Set.range f := ⟨f i, i, rfl⟩

def collision (i : I) (hi : i ≠ representative f (label f i)) : Collision f :=
  ⟨{i, representative f (label f i)}, Finset.card_pair hi, by
    intro j hj k hk
    have hj' : f j = f i := by
      rcases (show j = i ∨ j = representative f (label f i) by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hj) with rfl | rfl
      · rfl
      · exact representative_label f _
    have hk' : f k = f i := by
      rcases (show k = i ∨ k = representative f (label f i) by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hk) with rfl | rfl
      · rfl
      · exact representative_label f _
    exact hj'.trans hk'.symm⟩

/-- The distinguished occurrence uses its label; every further original
occurrence uses an actual unordered duplicate pair. -/
def encode (i : I) : Set.range f ⊕ Collision f :=
  if hi : i = representative f (label f i) then Sum.inl (label f i)
  else Sum.inr (collision f i hi)

theorem encode_injective : Function.Injective (encode f) := by
  intro i j hij
  by_cases hi : i = representative f (label f i) <;>
    by_cases hj : j = representative f (label f j)
  · have he : label f i = label f j := by simpa only [encode, dif_pos hi, dif_pos hj, Sum.inl.injEq] using hij
    exact hi.trans ((congrArg (representative f) he).trans hj.symm)
  · simp only [encode, dif_pos hi, dif_neg hj, Sum.inl_ne_inr] at hij
  · simp only [encode, dif_neg hi, dif_pos hj, Sum.inr_ne_inl] at hij
  · have he : collision f i hi = collision f j hj := by
      simpa only [encode, dif_neg hi, dif_neg hj, Sum.inr.injEq] using hij
    have hs := congrArg Subtype.val he
    have him : i ∈ (collision f j hj).val := hs ▸ Finset.mem_insert_self _ _
    have hfi : f i = f j :=
      (collision f j hj).property.2 i him j (Finset.mem_insert_self _ _)
    have hl : label f i = label f j := Subtype.ext hfi
    have hr : representative f (label f i) = representative f (label f j) :=
      congrArg (representative f) hl
    change i ∈ ({j, representative f (label f j)} : Finset I) at him
    rcases (show i = j ∨ i = representative f (label f j) by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using him) with heq | heq
    · exact heq
    · exact (hi (heq.trans hr.symm)).elim

/-- The complete original family, including all further coincidences. -/
theorem card_le_distinct_add_collisions [Finite I] :
    Nat.card I ≤ Nat.card (Set.range f) + Nat.card (Collision f) := by
  letI : Finite (Set.range f) := Finite.of_surjective (label f) (by
    rintro ⟨a,i,rfl⟩
    exact ⟨i,rfl⟩)
  have h := Nat.card_le_card_of_injective (encode f) (encode_injective f)
  simpa only [Nat.card_sum] using h

theorem excess_le_collisions [Finite I] :
    Nat.card I - Nat.card (Set.range f) ≤ Nat.card (Collision f) := by
  have h := card_le_distinct_add_collisions f
  omega

end SymmetricSubgroupAsymptotics.CharacterCollisionCount
