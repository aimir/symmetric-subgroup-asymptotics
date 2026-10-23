import Mathlib.GroupTheory.GroupAction.CardCommute
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Index

/-! Class count under an actual subgroup embedding, retaining its index.
Commuting pairs inject; cancellation of the subgroup order gives the
index factor. No monotonicity of class count under inclusion is asserted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ConjugacyClassSubgroupIndexBound

theorem class_card_le_index_mul {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) :
    Nat.card (ConjClasses H) ≤ H.index * Nat.card (ConjClasses G) := by
  let f : {p : H × H // Commute p.1 p.2} →
      {p : G × G // Commute p.1 p.2} := fun p =>
    ⟨(p.val.1.val,p.val.2.val),by
      change (p.val.1.val * p.val.2.val) = (p.val.2.val * p.val.1.val)
      exact congrArg Subtype.val p.property⟩
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun p => p.val.1) he
    · apply Subtype.ext
      exact congrArg (fun p => p.val.2) he
  have h := Nat.card_le_card_of_injective f hf
  rw [card_comm_eq_card_conjClasses_mul_card,
    card_comm_eq_card_conjClasses_mul_card,← H.card_mul_index] at h
  have h' : Nat.card (ConjClasses H) * Nat.card H ≤
      (H.index * Nat.card (ConjClasses G)) * Nat.card H := by
    simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h
  exact Nat.le_of_mul_le_mul_right h' (Nat.card_pos (α := H))

theorem class_card_le_injective_index {A G : Type*} [Group A] [Group G]
    [Finite A] [Finite G] (f : A →* G) (hf : Function.Injective f) :
    Nat.card (ConjClasses A) ≤ f.range.index * Nat.card (ConjClasses G) := by
  let e := MonoidHom.ofInjective hf
  have he : Nat.card (ConjClasses A) ≤ Nat.card (ConjClasses f.range) :=
    Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)
  exact he.trans (class_card_le_index_mul f.range)

end SymmetricSubgroupAsymptotics.ConjugacyClassSubgroupIndexBound
