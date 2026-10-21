import SymmetricSubgroupAsymptotics.BinaryElementaryPairMonomialWidth

/-! A common eight-dimensional shear space suffices for width six.

Variable zero is the inner physical pair variable. The allowed shear
monomials are the degree-at-most-two monomials in variables 1,2,3, together
with variable zero itself. This is weaker than allowing every quadratic
monomial in all four variables. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.BinaryThreeVariablePairMonomialWidth

open BinaryElementaryPairMonomialWidth

def Allowed (s : Finset (Fin 4)) : Prop :=
  (0 ∉ s ∧ s.card ≤ 2) ∨ s = {0}

def Raises (a b : Monomial) : Prop :=
  if a.1 then
    if b.1 then support b.2 ⊆ support a.2
    else Allowed (support b.2 \ support a.2)
  else b.1 = false ∧ support b.2 ⊆ support a.2

instance (a b : Monomial) : Decidable (Raises a b) := by
  unfold Raises Allowed
  infer_instance

private def baseChain : Fin 16 → Fin 6 :=
  ![0, 0, 1, 0, 2, 2, 1, 0, 3, 3, 4, 3, 5, 2, 1, 0]

private def swapLowTwo : Fin 16 → Fin 16 :=
  ![0, 2, 1, 3, 4, 6, 5, 7, 8, 10, 9, 11, 12, 14, 13, 15]

private def lowerColour : Fin 6 → Fin 6 := ![4, 2, 5, 1, 0, 3]

def chain (a : Monomial) : Fin 6 :=
  if a.1 then baseChain (swapLowTwo a.2) else lowerColour (baseChain a.2)

theorem raises_refl : ∀ a : Monomial, Raises a a := by decide

/-- Six chains, checked only on their individual monomial pairs. -/
theorem comparable_of_chain_eq : ∀ a b : Monomial,
    chain a = chain b → Raises a b ∨ Raises b a := by decide

theorem antichain_card_le_six (s : Finset Monomial)
    (hs : IsAntichain Raises (s : Set Monomial)) : s.card ≤ 6 := by
  classical
  have hinj : Set.InjOn chain (s : Set Monomial) := by
    intro a ha b hb he
    by_contra hne
    rcases comparable_of_chain_eq a b he with hab | hba
    · exact hs ha hb hne hab
    · exact hs hb ha (Ne.symm hne) hba
  calc
    s.card = (s.image chain).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ Fintype.card (Fin 6) := Finset.card_le_univ _
    _ = 6 := Fintype.card_fin 6

end SymmetricSubgroupAsymptotics.BinaryThreeVariablePairMonomialWidth
