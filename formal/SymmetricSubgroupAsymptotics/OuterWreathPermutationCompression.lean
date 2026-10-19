import SymmetricSubgroupAsymptotics.PermutationalWreathFinite
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.NormNum

/-! Generic faithful permutation compression of an actual outer wreath
embedding. No primitive profile or published input is assumed. The
one-factor case uses the regular action of the ACTUAL embedded group,
rather than padding its degree to the outer group's order. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics.OuterWreathPermutationCompression

abbrev Wreath (O : Type) [Group O] (k : ℕ) :=
  PermutationalWreathProduct O (Equiv.Perm (Fin k)) (Fin k)

def finitePointEquiv (A : Type) [Finite A] : A ≃ Fin (Nat.card A) :=
  Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card.symm)

def wreathPointEquiv (O : Type) [Finite O] (k : ℕ) :
    O × Fin k ≃ Fin (k * Nat.card O) :=
  (Equiv.prodComm O (Fin k)).trans
    ((Equiv.prodCongr (Equiv.refl (Fin k)) (finitePointEquiv O)).trans finProdFinEquiv)

/-- The base acts regularly on itself, and the top permutes the factors. -/
def wreathAction (O : Type) [Group O] [Finite O] (k : ℕ) :
    Wreath O k →* Equiv.Perm (Fin (k * Nat.card O)) :=
  (wreathPointEquiv O k).permCongrHom.toMonoidHom.comp
    (PermutationalWreathProduct.toPerm (D := O) (Q := Equiv.Perm (Fin k))
      (I := Fin k) (Lambda := O))

theorem wreathAction_injective (O : Type) [Group O] [Finite O]
    (k : ℕ) (hk : 0 < k) : Function.Injective (wreathAction O k) := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  exact (wreathPointEquiv O k).permCongrHom.injective.comp
    (PermutationalWreathProduct.toPerm_injective (D := O)
      (Q := Equiv.Perm (Fin k)) (I := Fin k) (Lambda := O))

variable {Q O : Type} [Group Q] [Group O] [Finite O] {k : ℕ}

/-- Compose the original embedded group, without replacing its carrier. -/
def compressedAction (f : Q →* Wreath O k) :
    Q →* Equiv.Perm (Fin (k * Nat.card O)) :=
  (wreathAction O k).comp f

theorem compressedAction_injective (f : Q →* Wreath O k)
    (hf : Function.Injective f) (hk : 0 < k) :
    Function.Injective (compressedAction f) :=
  (wreathAction_injective O k hk).comp hf

/-- The actual one-factor wreath has exactly the order of its base. -/
theorem wreath_one_card (O : Type) [Group O] [Finite O] :
    Nat.card (Wreath O 1) = Nat.card O := by
  rw [PermutationalWreathProduct.natCard_eq, Nat.card_fin, Nat.card_perm,
    Nat.card_fin]
  norm_num

theorem oneFactor_card_le [Finite Q] (f : Q →* Wreath O 1)
    (hf : Function.Injective f) : Nat.card Q ≤ Nat.card O :=
  (Nat.card_le_card_of_injective f hf).trans_eq (wreath_one_card O)

/-- A genuine regular action on the original group, of its exact order. -/
def regularAction (Q : Type) [Group Q] [Finite Q] :
    Q →* Equiv.Perm (Fin (Nat.card Q)) :=
  (finitePointEquiv Q).permCongrHom.toMonoidHom.comp (MulAction.toPermHom Q Q)

theorem regularAction_injective (Q : Type) [Group Q] [Finite Q] :
    Function.Injective (regularAction Q) :=
  (finitePointEquiv Q).permCongrHom.injective.comp MulAction.toPerm_injective

/-- In the one-factor case the degree is exactly the actual quotient order,
while its comparison with the outer order is derived from the embedding. -/
theorem oneFactor_regular_compression [Finite Q] (f : Q →* Wreath O 1)
    (hf : Function.Injective f) :
    0 < Nat.card Q ∧ Nat.card Q ≤ Nat.card O ∧
      Function.Injective (regularAction Q) :=
  ⟨Nat.card_pos, oneFactor_card_le f hf, regularAction_injective Q⟩

end SymmetricSubgroupAsymptotics.OuterWreathPermutationCompression
