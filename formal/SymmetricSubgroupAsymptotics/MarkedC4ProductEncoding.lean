import SymmetricSubgroupAsymptotics.MarkedC4ErrorCalculus

/-!
# Product encodings with an unmarked auxiliary coordinate

RDT Lemma 2.7 encodes a nilpotent permutation group by its binary grid word
and an odd-order auxiliary object.  Every homomorphism to `C4` is determined
by the binary part.  This file is the abstract weighted summation theorem for
that situation.  It assumes only an injective unmarked code and a pointwise
Hom-cardinality comparison.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace MarkedC4

/-- An injective code into a marked core and an unmarked auxiliary object. -/
structure ProductEncoding
    (A B C : Type*) [Fintype A] [Fintype B] [Fintype C]
    (source : A → Type*) (target : B → Type*)
    [∀ a, Group (source a)] [∀ a, Finite (source a)]
    [∀ q, Group (target q)] [∀ q, Finite (target q)] where
  code : A → B × C
  code_injective : Function.Injective code
  hom_card : ∀ a,
    Nat.card (source a →* Multiplicative (ZMod 4)) ≤
      Nat.card (target (code a).1 →* Multiplicative (ZMod 4))

namespace ProductEncoding

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
  {source : A → Type*} {target : B → Type*}
  [∀ a, Group (source a)] [∀ a, Finite (source a)]
  [∀ q, Group (target q)] [∀ q, Finite (target q)]

theorem fibre_card_le_one
    (E : ProductEncoding A B C source target) (z : B × C) :
    Nat.card {a : A // E.code a = z} ≤ 1 := by
  rw [Finite.card_le_one_iff_subsingleton]
  exact ⟨fun x y =>
    Subtype.ext (E.code_injective (x.property.trans y.property.symm))⟩

/-- All marked weight stays on the retained core; the auxiliary coordinate
costs only its unmarked cardinality. -/
theorem homMoment_sum_le
    (E : ProductEncoding A B C source target) (r : ℕ) :
    (∑ a : A,
        (Nat.card (source a →* Multiplicative (ZMod 4)) : ℝ) ^ r) ≤
      (Fintype.card C : ℝ) *
        ∑ q : B,
          (Nat.card (target q →* Multiplicative (ZMod 4)) : ℝ) ^ r := by
  have hsum := sum_le_uniformFiber_mul_sum E.code
    (fun a : A =>
      (Nat.card (source a →* Multiplicative (ZMod 4)) : ℝ) ^ r)
    (fun z : B × C =>
      (Nat.card (target z.1 →* Multiplicative (ZMod 4)) : ℝ) ^ r)
    1 1 (fun a => by
      norm_num
      exact_mod_cast Nat.pow_le_pow_left (E.hom_card a) r)
    (by norm_num) (fun _ => by positivity) E.fibre_card_le_one
  have hproduct :
      (∑ z : B × C,
          (Nat.card (target z.1 →* Multiplicative (ZMod 4)) : ℝ) ^ r) =
        (Fintype.card C : ℝ) *
          ∑ q : B,
            (Nat.card (target q →* Multiplicative (ZMod 4)) : ℝ) ^ r := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ q : B, ∑ _c : C,
          (Nat.card (target q →* Multiplicative (ZMod 4)) : ℝ) ^ r) =
          ∑ q : B, (Fintype.card C : ℝ) *
            (Nat.card (target q →* Multiplicative (ZMod 4)) : ℝ) ^ r := by
        apply Finset.sum_congr rfl
        intro q hq
        simp
      _ = (Fintype.card C : ℝ) *
          ∑ q : B,
            (Nat.card (target q →* Multiplicative (ZMod 4)) : ℝ) ^ r := by
        rw [Finset.mul_sum]
  calc
    _ ≤ (1 : ℝ) * 1 *
        ∑ z : B × C,
          (Nat.card (target z.1 →* Multiplicative (ZMod 4)) : ℝ) ^ r := by
      simpa only [Nat.cast_one] using hsum
    _ = _ := by rw [one_mul, one_mul, hproduct]

end ProductEncoding

end MarkedC4
end SymmetricSubgroupAsymptotics

end
