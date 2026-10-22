import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingEdges
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingTwins
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-! Exact transport between the three original (possibly different)
flag-coordinate types and the dependent Fin3 product used by the proved
Hamming direction theorem. No cardinality identification is needed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingEdges
open CFSGOrthogonalDIndexTrialityD4HammingTwins
variable (A B C : Type)

def TripleFamily (i : Fin 3) : Type := Fin.cases A (Fin.cases B (fun _ => C)) i

def tripleEquiv : A × (B × C) ≃ ((i : Fin 3) → TripleFamily A B C i) where
  toFun p := Fin.cases p.1 (Fin.cases p.2.1 (fun _ => p.2.2))
  invFun x := (x 0, (x 1, x 2))
  left_inv p := rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl

instance tripleFamilyNontrivial [Nontrivial A] [Nontrivial B] [Nontrivial C]
    (i : Fin 3) : Nontrivial (TripleFamily A B C i) := by
  fin_cases i
  · change Nontrivial A
    infer_instance
  · change Nontrivial B
    infer_instance
  · change Nontrivial C
    infer_instance

theorem triple_closedAdjacent_iff (p q : A × (B × C)) :
    ClosedAdjacent (tripleEquiv A B C p) (tripleEquiv A B C q) ↔ TwoCoordinates p q := by
  constructor
  · intro h
    by_cases h0 : p.1 = q.1
    · by_cases h1 : p.2.1 = q.2.1
      · exact Or.inl ⟨h0, h1⟩
      · by_cases h2 : p.2.2 = q.2.2
        · exact Or.inr (Or.inl ⟨h0, h2⟩)
        · have hh : (1 : Fin 3) = 2 := h 1 2 h1 h2
          exact False.elim ((by decide : (1 : Fin 3) ≠ 2) hh)
    · by_cases h1 : p.2.1 = q.2.1
      · by_cases h2 : p.2.2 = q.2.2
        · exact Or.inr (Or.inr ⟨h1, h2⟩)
        · have hh : (0 : Fin 3) = 2 := h 0 2 h0 h2
          exact False.elim ((by decide : (0 : Fin 3) ≠ 2) hh)
      · have hh : (0 : Fin 3) = 1 := h 0 1 h0 h1
        exact False.elim ((by decide : (0 : Fin 3) ≠ 1) hh)
  · rintro (⟨h0, h1⟩ | ⟨h0, h2⟩ | ⟨h1, h2⟩)
    · apply closedAdjacent_of_axis (2 : Fin 3)
      intro j hj
      fin_cases j
      · exact h0
      · exact h1
      · exact False.elim (hj rfl)
    · apply closedAdjacent_of_axis (1 : Fin 3)
      intro j hj
      fin_cases j
      · exact h0
      · exact False.elim (hj rfl)
      · exact h2
    · apply closedAdjacent_of_axis (0 : Fin 3)
      intro j hj
      fin_cases j
      · exact False.elim (hj rfl)
      · exact h1
      · exact h2

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingEdges
