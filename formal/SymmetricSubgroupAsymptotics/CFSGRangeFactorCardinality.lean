import Mathlib.SetTheory.Cardinal.Finite

/-! A literal factor on ranges cannot increase finite cardinality. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGRangeFactorCardinality

theorem card_range_le_of_factor {A B C : Type*} (f : A → B) (g : A → C)
    [Finite (Set.range f)] (hfactor : ∀ a b, f a = f b → g a = g b) :
    Nat.card (Set.range g) ≤ Nat.card (Set.range f) := by
  let rep (x : Set.range f) : A := Classical.choose x.property
  have hrep (x : Set.range f) : f (rep x) = x.val := Classical.choose_spec x.property
  let lift : Set.range f → Set.range g := fun x => ⟨g (rep x), ⟨rep x, rfl⟩⟩
  have hsurj : Function.Surjective lift := by
    rintro ⟨_, a, rfl⟩
    refine ⟨⟨f a, ⟨a, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    exact hfactor _ _ (hrep ⟨f a, ⟨a, rfl⟩⟩)
  exact Nat.card_le_card_of_surjective lift hsurj

end SymmetricSubgroupAsymptotics.CFSGRangeFactorCardinality
