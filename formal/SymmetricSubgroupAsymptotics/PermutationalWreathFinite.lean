import SymmetricSubgroupAsymptotics.PermutationalWreathProduct
import Mathlib.Data.Finite.Card

/-!
# Finite cardinality of a permutational wreath product

The project's permutational wreath product is definitionally a base
function together with a top element.  This file records that underlying
equivalence and its cardinality, without changing the group law.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PermutationalWreathProduct

variable {D Q I : Type*} [Group D] [Group Q] [MulAction Q I]

/-- The underlying finite set of a permutational wreath product. -/
def equivProd :
    PermutationalWreathProduct D Q I ≃ (I → D) × Q where
  toFun w := (w.left, w.right)
  invFun w := ⟨w.1, w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Finite D] [Finite Q] [Finite I] :
    Finite (PermutationalWreathProduct D Q I) :=
  Finite.of_equiv ((I → D) × Q) equivProd.symm

/-- Exact cardinality of the literal permutational wreath product. -/
theorem natCard_eq [Finite D] [Finite Q] [Finite I] :
    Nat.card (PermutationalWreathProduct D Q I) =
      Nat.card D ^ Nat.card I * Nat.card Q := by
  rw [Nat.card_congr equivProd, Nat.card_prod, Nat.card_fun]

end PermutationalWreathProduct
end SymmetricSubgroupAsymptotics

end
