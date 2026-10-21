import SymmetricSubgroupAsymptotics.BinaryElementaryPairMonomialWidth

/-! One selected pair of missing quadratic leading shears;32 labels only. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.BinaryFourQuadraticAdjacentWidth
open BinaryElementaryPairMonomialWidth

def Allowed (s : Finset (Fin 4)) : Prop :=
 s.card ≤ 1 ∨ (s.card = 2 ∧ s ≠ support 3 ∧ s ≠ support 5)
instance (s : Finset (Fin 4)) : Decidable (Allowed s) := by unfold Allowed; infer_instance

def Raises (a b : Monomial) : Prop :=
 if a.1 then (if b.1 then support b.2 ⊆ support a.2 else Allowed (support b.2 \ support a.2))
 else b.1 = false ∧ support b.2 ⊆ support a.2
instance (a b : Monomial) : Decidable (Raises a b) := by unfold Raises; infer_instance
private def colors : Fin 32 → Fin 7 := ![4, 4, 1, 4, 2, 2, 1, 4, 0, 0, 5, 5, 3, 0, 3, 4, 1, 5, 1, 5, 0, 0, 4, 0, 3, 3, 1, 1, 2, 3, 4, 5]
def chain (a : Monomial) : Fin 7 := colors
 (if a.1 then ⟨16+a.2.val,by omega⟩ else ⟨a.2.val,by omega⟩)
theorem raises_refl : ∀ a : Monomial, Raises a a := by decide
theorem comparable : ∀ a b : Monomial, chain a = chain b → Raises a b ∨ Raises b a := by decide

theorem antichain_card_le_seven (s : Finset Monomial)
 (hs : IsAntichain Raises (s : Set Monomial)) : s.card ≤ 7 := by
 classical
 have hinj : Set.InjOn chain (s : Set Monomial) := by
  intro a ha b hb he
  by_contra hne
  rcases comparable a b he with hab | hba
  · exact hs ha hb hne hab
  · exact hs hb ha (Ne.symm hne) hba
 calc
  s.card = (s.image chain).card := (Finset.card_image_of_injOn hinj).symm
  _ ≤ Fintype.card (Fin 7) := Finset.card_le_univ _
  _ = 7 := Fintype.card_fin 7
end SymmetricSubgroupAsymptotics.BinaryFourQuadraticAdjacentWidth
