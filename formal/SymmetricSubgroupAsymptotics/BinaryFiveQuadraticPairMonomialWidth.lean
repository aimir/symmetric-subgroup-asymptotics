import SymmetricSubgroupAsymptotics.BinaryElementaryPairMonomialWidth
import Mathlib.Tactic.FinCases

/-! Seven chains after retaining five of the six quadratic shears.
The certificate ranges only over the six missing monomials and 32 labels. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.BinaryFiveQuadraticPairMonomialWidth

open BinaryElementaryPairMonomialWidth

def missing (j : Fin 6) : Fin 16 := ![3, 5, 6, 9, 10, 12] j

def Allowed (j : Fin 6) (s : Finset (Fin 4)) : Prop :=
  s.card ≤ 1 ∨ (s.card = 2 ∧ s ≠ support (missing j))

instance (j : Fin 6) (s : Finset (Fin 4)) : Decidable (Allowed j s) := by
  unfold Allowed
  infer_instance

def Raises (j : Fin 6) (a b : Monomial) : Prop :=
  if a.1 then
    if b.1 then support b.2 ⊆ support a.2
    else Allowed j (support b.2 \ support a.2)
  else b.1 = false ∧ support b.2 ⊆ support a.2

instance (j : Fin 6) (a b : Monomial) : Decidable (Raises j a b) := by
  unfold Raises
  infer_instance

private def chains : Fin 6 → Fin 32 → Fin 7 :=
  ![![1, 1, 4, 1, 2, 2, 4, 1, 5, 5, 0, 5, 3, 3, 0, 1, 4, 5, 4, 5, 0, 0, 4, 0, 3, 3, 1, 1, 2, 3, 4, 5],
    ![2, 2, 5, 2, 4, 4, 5, 4, 3, 3, 1, 3, 0, 0, 1, 4, 5, 5, 1, 5, 0, 0, 4, 0, 3, 3, 1, 1, 2, 3, 4, 5],
    ![2, 2, 1, 2, 5, 5, 1, 1, 3, 3, 4, 3, 0, 0, 4, 1, 5, 5, 4, 5, 0, 0, 4, 0, 3, 3, 1, 1, 2, 3, 4, 5],
    ![2, 2, 1, 2, 5, 5, 1, 1, 3, 3, 4, 3, 0, 0, 4, 1, 5, 0, 5, 5, 4, 0, 4, 0, 3, 3, 1, 1, 2, 3, 4, 5],
    ![2, 2, 1, 2, 5, 5, 1, 1, 3, 3, 4, 3, 0, 0, 4, 1, 5, 5, 4, 5, 0, 0, 4, 0, 3, 3, 1, 1, 2, 3, 4, 5],
    ![2, 2, 4, 2, 5, 5, 4, 4, 3, 3, 1, 3, 0, 0, 1, 1, 5, 5, 4, 5, 0, 0, 4, 0, 3, 3, 1, 1, 2, 3, 4, 5]]

def chain (j : Fin 6) (a : Monomial) : Fin 7 :=
  chains j (if a.1 then ⟨16 + a.2.val, by omega⟩ else ⟨a.2.val, by omega⟩)

theorem raises_refl : ∀ j : Fin 6, ∀ a : Monomial, Raises j a a := by decide

private theorem comparable_case_0 : ∀ a b : Monomial,
    chain 0 a = chain 0 b → Raises 0 a b ∨ Raises 0 b a := by decide

private theorem comparable_case_1 : ∀ a b : Monomial,
    chain 1 a = chain 1 b → Raises 1 a b ∨ Raises 1 b a := by decide

private theorem comparable_case_2 : ∀ a b : Monomial,
    chain 2 a = chain 2 b → Raises 2 a b ∨ Raises 2 b a := by decide

private theorem comparable_case_3 : ∀ a b : Monomial,
    chain 3 a = chain 3 b → Raises 3 a b ∨ Raises 3 b a := by decide

private theorem comparable_case_4 : ∀ a b : Monomial,
    chain 4 a = chain 4 b → Raises 4 a b ∨ Raises 4 b a := by decide

private theorem comparable_case_5 : ∀ a b : Monomial,
    chain 5 a = chain 5 b → Raises 5 a b ∨ Raises 5 b a := by decide

theorem comparable_of_chain_eq : ∀ j : Fin 6, ∀ a b : Monomial,
    chain j a = chain j b → Raises j a b ∨ Raises j b a := by
  intro j
  fin_cases j
  · exact comparable_case_0
  · exact comparable_case_1
  · exact comparable_case_2
  · exact comparable_case_3
  · exact comparable_case_4
  · exact comparable_case_5


theorem antichain_card_le_seven (j : Fin 6) (s : Finset Monomial)
    (hs : IsAntichain (Raises j) (s : Set Monomial)) : s.card ≤ 7 := by
  classical
  have hinj : Set.InjOn (chain j) (s : Set Monomial) := by
    intro a ha b hb he
    by_contra hne
    rcases comparable_of_chain_eq j a b he with hab | hba
    · exact hs ha hb hne hab
    · exact hs hb ha (Ne.symm hne) hba
  calc
    s.card = (s.image (chain j)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ Fintype.card (Fin 7) := Finset.card_le_univ _
    _ = 7 := Fintype.card_fin 7

end SymmetricSubgroupAsymptotics.BinaryFiveQuadraticPairMonomialWidth
