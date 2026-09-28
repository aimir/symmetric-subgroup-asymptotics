import SymmetricSubgroupAsymptotics.FusionEpimorphismLifts
import SymmetricSubgroupAsymptotics.PrimeAbelianization

/-!
# Epimorphisms to an elementary prime target

The complete scalar-character space of the original source gives an exact
count of all homomorphisms to a finite prime-field vector group.  Passing to
onto maps is only an inclusion.  This is uniform in the prime and keeps an
actual target equivalence rather than replacing the target by its order.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]

variable (G : Type*) [Group G]
variable {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

/-- Multiplicative homomorphisms to a prime-field vector group factor
uniquely through the actual prime abelianization of the same source. -/
def primeAbelianizationGroupHomEquiv [Finite G] [Finite V] :
    (G →* Multiplicative V) ≃
      (PrimeAbelianization p G →ₗ[ZMod p] V) :=
  AddMonoidHom.toMultiplicativeRight.symm.trans
    (primeAbelianizationHomEquiv p G)

/-- Exact cardinality of all maps to an elementary prime target. -/
theorem primeAbelianizationGroupHom_card [Finite G] [Finite V] :
    Nat.card (G →* Multiplicative V) =
      p ^ (Module.finrank (ZMod p) (PrimeCharacters p G) *
        Module.finrank (ZMod p) V) := by
  rw [Nat.card_congr (primeAbelianizationGroupHomEquiv p G),
    Module.natCard_eq_pow_finrank (K := ZMod p), Module.finrank_linearMap,
    Subspace.dual_finrank_eq, Nat.card_zmod]

variable {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q]

/-- Onto maps to an actual elementary target are bounded through the stated
target equivalence.  No presentation or chosen basis of the target group is
used. -/
theorem groupEpimorphism_card_le_elementary
    [Finite V] (e : Q ≃* Multiplicative V) :
    Nat.card (GroupEpimorphism G Q) ≤
      p ^ (Module.finrank (ZMod p) (PrimeCharacters p G) *
        Module.finrank (ZMod p) V) := by
  letI : Finite (G →* Q) :=
    Finite.of_injective (fun f : G →* Q => (f : G → Q)) DFunLike.coe_injective
  calc
    Nat.card (GroupEpimorphism G Q) ≤ Nat.card (G →* Q) :=
      Nat.card_le_card_of_injective (fun β : GroupEpimorphism G Q ↦ β.1)
        (fun _ _ h ↦ Subtype.ext h)
    _ = Nat.card (G →* Multiplicative V) := by
      rw [Nat.card_congr e.monoidHomCongrRightEquiv]
    _ = _ := primeAbelianizationGroupHom_card p G

/-- Rank-at-most-two form used by the elementary quotients of a
degree-nine ternary top. -/
theorem groupEpimorphism_card_le_elementary_rank_two
    [Finite V] (e : Q ≃* Multiplicative V)
    (hrank : Module.finrank (ZMod p) V ≤ 2) :
    Nat.card (GroupEpimorphism G Q) ≤
      p ^ (2 * Module.finrank (ZMod p) (PrimeCharacters p G)) := by
  refine (groupEpimorphism_card_le_elementary p e).trans ?_
  apply Nat.pow_le_pow_right (Fact.out : p.Prime).pos
  nlinarith [Nat.mul_le_mul_left
    (Module.finrank (ZMod p) (PrimeCharacters p G)) hrank]

end SymmetricSubgroupAsymptotics

end
