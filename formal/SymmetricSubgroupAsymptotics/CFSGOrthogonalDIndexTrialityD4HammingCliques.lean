import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingTwins
import Mathlib.Data.Set.Basic

/-! Genuine coordinate-clique classification in a three-factor
Hamming residue. This is a combinatorial prerequisite for recognizing
the three local triality directions, not a global coherence axiom. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingTwins
variable {A B C : Type*}

def FirstAxis (b : B) (c : C) : Set (A × (B × C)) := {p | p.2.1 = b ∧ p.2.2 = c}
def SecondAxis (a : A) (c : C) : Set (A × (B × C)) := {p | p.1 = a ∧ p.2.2 = c}
def ThirdAxis (a : A) (b : B) : Set (A × (B × C)) := {p | p.1 = a ∧ p.2.1 = b}

def CoordinateClique (S : Set (A × (B × C))) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, TwoCoordinates a b

theorem firstAxis_clique (b : B) (c : C) : CoordinateClique (FirstAxis b c : Set (A × (B × C))) := by
  intro x hx y hy
  exact Or.inr (Or.inr ⟨hx.1.trans hy.1.symm, hx.2.trans hy.2.symm⟩)

theorem secondAxis_clique (a : A) (c : C) : CoordinateClique (SecondAxis a c : Set (A × (B × C))) := by
  intro x hx y hy
  exact Or.inr (Or.inl ⟨hx.1.trans hy.1.symm, hx.2.trans hy.2.symm⟩)

theorem thirdAxis_clique (a : A) (b : B) : CoordinateClique (ThirdAxis a b : Set (A × (B × C))) := by
  intro x hx y hy
  exact Or.inl ⟨hx.1.trans hy.1.symm, hx.2.trans hy.2.symm⟩

theorem twoCoordinates_swap01 (a b : A × (B × C)) :
    TwoCoordinates (a.2.1, (a.1, a.2.2)) (b.2.1, (b.1, b.2.2)) ↔ TwoCoordinates a b := by
  constructor
  · rintro (⟨h1, h0⟩ | ⟨h1, h2⟩ | ⟨h0, h2⟩)
    · exact Or.inl ⟨h0, h1⟩
    · exact Or.inr (Or.inr ⟨h1, h2⟩)
    · exact Or.inr (Or.inl ⟨h0, h2⟩)
  · rintro (⟨h0, h1⟩ | ⟨h0, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h1, h0⟩
    · exact Or.inr (Or.inr ⟨h0, h2⟩)
    · exact Or.inr (Or.inl ⟨h1, h2⟩)

theorem twoCoordinates_swap02 (a b : A × (B × C)) :
    TwoCoordinates (a.2.2, (a.2.1, a.1)) (b.2.2, (b.2.1, b.1)) ↔ TwoCoordinates a b := by
  constructor
  · rintro (⟨h2, h1⟩ | ⟨h2, h0⟩ | ⟨h1, h0⟩)
    · exact Or.inr (Or.inr ⟨h1, h2⟩)
    · exact Or.inr (Or.inl ⟨h0, h2⟩)
    · exact Or.inl ⟨h0, h1⟩
  · rintro (⟨h0, h1⟩ | ⟨h0, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inr (Or.inr ⟨h1, h0⟩)
    · exact Or.inr (Or.inl ⟨h2, h0⟩)
    · exact Or.inl ⟨h2, h1⟩

theorem common_neighbors_first_difference (a b x : A × (B × C))
    (hne : a.1 ≠ b.1) (hab : TwoCoordinates a b)
    (hxa : TwoCoordinates x a) (hxb : TwoCoordinates x b) :
    x ∈ FirstAxis a.2.1 a.2.2 := by
  have h12 : a.2.1 = b.2.1 ∧ a.2.2 = b.2.2 := by
    rcases hab with ⟨h0, _⟩ | ⟨h0, _⟩ | h12
    · exact False.elim (hne h0)
    · exact False.elim (hne h0)
    · exact h12
  rcases hxa with ⟨h0, h1⟩ | ⟨h0, h2⟩ | h12'
  · rcases hxb with ⟨k0, _⟩ | ⟨k0, _⟩ | ⟨_, k2⟩
    · exact False.elim (hne (h0.symm.trans k0))
    · exact False.elim (hne (h0.symm.trans k0))
    · exact ⟨h1, k2.trans h12.2.symm⟩
  · rcases hxb with ⟨k0, _⟩ | ⟨k0, _⟩ | ⟨k1, _⟩
    · exact False.elim (hne (h0.symm.trans k0))
    · exact False.elim (hne (h0.symm.trans k0))
    · exact ⟨k1.trans h12.1.symm, h2⟩
  · exact h12'

theorem clique_contained_axis (S : Set (A × (B × C))) (hS : CoordinateClique S)
    (a b : A × (B × C)) (ha : a ∈ S) (hb : b ∈ S) (hne : a ≠ b) :
    S ⊆ FirstAxis a.2.1 a.2.2 ∨ S ⊆ SecondAxis a.1 a.2.2 ∨ S ⊆ ThirdAxis a.1 a.2.1 := by
  classical
  by_cases h0 : a.1 = b.1
  · by_cases h1 : a.2.1 = b.2.1
    · have h2 : a.2.2 ≠ b.2.2 := fun h => hne (Prod.ext h0 (Prod.ext h1 h))
      right; right
      intro x hx
      have hh := common_neighbors_first_difference
        (a.2.2, (a.2.1, a.1)) (b.2.2, (b.2.1, b.1)) (x.2.2, (x.2.1, x.1)) h2
        ((twoCoordinates_swap02 a b).mpr (hS a ha b hb))
        ((twoCoordinates_swap02 x a).mpr (hS x hx a ha))
        ((twoCoordinates_swap02 x b).mpr (hS x hx b hb))
      exact ⟨hh.2, hh.1⟩
    · right; left
      intro x hx
      exact common_neighbors_first_difference
        (a.2.1, (a.1, a.2.2)) (b.2.1, (b.1, b.2.2)) (x.2.1, (x.1, x.2.2)) h1
        ((twoCoordinates_swap01 a b).mpr (hS a ha b hb))
        ((twoCoordinates_swap01 x a).mpr (hS x hx a ha))
        ((twoCoordinates_swap01 x b).mpr (hS x hx b hb))
  · left
    intro x hx
    exact common_neighbors_first_difference a b x h0 (hS a ha b hb)
      (hS x hx a ha) (hS x hx b hb)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingTwins
