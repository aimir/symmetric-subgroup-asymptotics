import Mathlib.Logic.Equiv.Defs

/-! In a three-factor Hamming residue, distinct coordinate triples
have distinct closed neighbourhoods. Under a surjective coordinate
map this identifies true-twin fibres exactly, without a coherence or
building-classification assumption. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingTwins
variable {A B C X : Type*} [Nontrivial A] [Nontrivial B] [Nontrivial C]

def TwoCoordinates (a b : A × (B × C)) : Prop :=
  (a.1 = b.1 ∧ a.2.1 = b.2.1) ∨
    (a.1 = b.1 ∧ a.2.2 = b.2.2) ∨ (a.2.1 = b.2.1 ∧ a.2.2 = b.2.2)

theorem twoCoordinates_refl (a : A × (B × C)) : TwoCoordinates a a :=
  Or.inl ⟨rfl, rfl⟩

theorem twoCoordinates_symm (a b : A × (B × C)) :
    TwoCoordinates a b ↔ TwoCoordinates b a := by
  simp only [TwoCoordinates, eq_comm]

theorem coordinates_eq_of_closed_neighborhoods (a b : A × (B × C))
    (h : ∀ z, TwoCoordinates a z ↔ TwoCoordinates b z) : a = b := by
  classical
  have hab : TwoCoordinates b a := (h a).mp (twoCoordinates_refl a)
  by_cases h0 : a.1 = b.1
  · by_cases h1 : a.2.1 = b.2.1
    · by_cases h2 : a.2.2 = b.2.2
      · exact Prod.ext h0 (Prod.ext h1 h2)
      · obtain ⟨c, hc⟩ := exists_ne a.1
        have ha : TwoCoordinates a (c, (a.2.1, a.2.2)) := Or.inr (Or.inr ⟨rfl, rfl⟩)
        have hb := (h (c, (a.2.1, a.2.2))).mp ha
        rcases hb with ⟨hb, _⟩ | ⟨hb, _⟩ | ⟨_, hb⟩
        · exact False.elim (hc (hb.symm.trans h0.symm))
        · exact False.elim (hc (hb.symm.trans h0.symm))
        · exact False.elim (h2 hb.symm)
    · have h2 : a.2.2 = b.2.2 := by
        rcases hab with ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨hb, _⟩
        · exact False.elim (h1 hb.symm)
        · exact hb.symm
        · exact False.elim (h1 hb.symm)
      obtain ⟨c, hc⟩ := exists_ne a.2.2
      have ha : TwoCoordinates a (a.1, (a.2.1, c)) := Or.inl ⟨rfl, rfl⟩
      have hb := (h (a.1, (a.2.1, c))).mp ha
      rcases hb with ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨hb, _⟩
      · exact False.elim (h1 hb.symm)
      · exact False.elim (hc (hb.symm.trans h2.symm))
      · exact False.elim (h1 hb.symm)
  · have h1 : a.2.1 = b.2.1 := by
      rcases hab with ⟨hb, _⟩ | ⟨hb, _⟩ | ⟨hb, _⟩
      · exact False.elim (h0 hb.symm)
      · exact False.elim (h0 hb.symm)
      · exact hb.symm
    obtain ⟨c, hc⟩ := exists_ne a.2.1
    have ha : TwoCoordinates a (a.1, (c, a.2.2)) := Or.inr (Or.inl ⟨rfl, rfl⟩)
    have hb := (h (a.1, (c, a.2.2))).mp ha
    rcases hb with ⟨hb, _⟩ | ⟨hb, _⟩ | ⟨hb, _⟩
    · exact False.elim (h0 hb.symm)
    · exact False.elim (h0 hb.symm)
    · exact False.elim (hc (hb.symm.trans h1.symm))

theorem coordinate_fibres_eq_true_twins (f : X → A × (B × C))
    (hf : Function.Surjective f) (x y : X) :
    (∀ z, TwoCoordinates (f x) (f z) ↔ TwoCoordinates (f y) (f z)) ↔ f x = f y := by
  constructor
  · intro h
    apply coordinates_eq_of_closed_neighborhoods
    intro a
    obtain ⟨z, rfl⟩ := hf a
    exact h z
  · intro h z
    rw [h]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingTwins
