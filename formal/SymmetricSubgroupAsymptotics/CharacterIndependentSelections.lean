import SymmetricSubgroupAsymptotics.IndependentBinarySelections
import Mathlib.Data.Fintype.Powerset

/-!
# Independent selections among original character occurrences

Distinct labels are represented by original occurrences. This embeds the
greedy independent selections into the complete original occurrence family;
all other equal characters remain present. No point-orbit fusion or global
moment bound is supplied by this combinatorial statement.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.CharacterIndependentSelections

variable {I V : Type*} [Finite I] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (f : I → V)

def labels : Finset V := Finset.univ.image f

def labelEquiv : labels f ≃ Set.range f :=
  Equiv.subtypeEquivRight (fun v => by simp [labels, Set.mem_range])

theorem labels_card : (labels f).card = Nat.card (Set.range f) := by
  have h := Nat.card_congr (labelEquiv f)
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at h
  exact h

def representative (v : labels f) : I := (Finset.mem_image.mp v.property).choose

theorem representative_spec (v : labels f) : f (representative f v) = v.val :=
  (Finset.mem_image.mp v.property).choose_spec.2

/-- Actual ordered occurrence selections with joint independent labels. -/
abbrev Frame (n : ℕ) := {v : Fin n → I // LinearIndependent (ZMod 2) (f ∘ v)}

def liftFrame {n : ℕ} (v : IndependentBinarySelections.Frame (labels f) n) : Frame f n :=
  ⟨fun j => representative f (v.val j), by
    have he : (f ∘ fun j => representative f (v.val j)) = fun j => (v.val j : V) := by
      funext j
      exact representative_spec f _
    rw [he]
    exact v.property⟩

theorem liftFrame_injective {n : ℕ} : Function.Injective (liftFrame f (n := n)) := by
  intro v w h
  apply Subtype.ext
  funext j
  apply Subtype.ext
  have he := congrArg (fun z : Frame f n => f (z.val j)) h
  simpa only [liftFrame, representative_spec] using he

/-- The full original character family contains enough independent
four-selections to control its distinct-label count. -/
theorem four_frame_card_lower (hzero : ∀ i, f i ≠ 0) :
    (Nat.card (Set.range f) - 7) ^ 4 ≤ Nat.card (Frame f 4) := by
  have hz : (0 : V) ∉ labels f := by
    intro h
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
    exact hzero i hi
  have h := IndependentBinarySelections.four_frame_card_lower (labels f) hz
  rw [labels_card] at h
  exact h.trans (Nat.card_le_card_of_injective (liftFrame f) (liftFrame_injective f))

end SymmetricSubgroupAsymptotics.CharacterIndependentSelections
