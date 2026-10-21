import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Antichain

/-! Six chains for the two-layer, four-variable monomial relation.

The true layer consists of the monomials containing the pair variable.
Within either layer, difference operators remove variables. Across layers,
pointwise multiplication by a squarefree polynomial of degree at most two
can add at most two variables before further difference operators act.
This relation concerns 32 individual monomials, not families of submodules. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.BinaryElementaryPairMonomialWidth

abbrev Monomial := Bool × Fin 16

def support (a : Fin 16) : Finset (Fin 4) :=
  Finset.univ.filter fun i => a.val.testBit i.val

def Raises (a b : Monomial) : Prop :=
  if a.1 then
    if b.1 then support b.2 ⊆ support a.2
    else (support b.2 \ support a.2).card ≤ 2
  else b.1 = false ∧ support b.2 ⊆ support a.2

instance (a b : Monomial) : Decidable (Raises a b) := by
  unfold Raises
  infer_instance

private def upperChain : Fin 16 → Fin 6 :=
  ![0, 0, 1, 0, 2, 2, 1, 0, 3, 3, 4, 3, 5, 2, 1, 0]

/-- The lower chains exchange the empty-to-full chain and the singleton
chain indexed by the mask 10. This makes the cross-layer joins valid. -/
def chain (a : Monomial) : Fin 6 :=
  if a.1 then upperChain a.2
  else if upperChain a.2 = 0 then 4
    else if upperChain a.2 = 4 then 0 else upperChain a.2

theorem raises_refl : ∀ a : Monomial, Raises a a := by decide

/-- This checks only the 32 by 32 monomial pairs in six displayed chains. -/
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

end SymmetricSubgroupAsymptotics.BinaryElementaryPairMonomialWidth
