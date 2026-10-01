import SymmetricSubgroupAsymptotics.MarkedC4SolubleReduction

/-!
# Mark transport through permutation-group encodings

Several RDT reductions use the same unmarked code: retain a subgroup `K`,
adjoin at most `l` displayed generators, and record enough ambient data that
the source subgroup is recovered.  This file proves once that any such
injective code transports the entire marked sum with factor

`|X|^l * 4^(r*l)`,

where `X` is the literal alphabet used by the unmarked code.  Taking
`X = S_b` gives the bounded-source generation step; the large-orbit step can
retain its much smaller soluble-container alphabet.

The interface contains no marked bound on the target family.  It asks only
for the literal retained subgroup, relative generators, equality of its Hom
count with the target code, and injectivity of the unmarked code.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace MarkedC4

/-- An injective relative-generator encoding from a finite family `A` of
literal permutation subgroups to a finite target family `B`. -/
structure PermutationRelativeGeneratorEncoding
    (b l : ℕ) (A B X : Type*) [Fintype A] [Fintype B] [Fintype X]
    (source : A → Subgroup (PermutationGroup b))
    (target : B → Subgroup (PermutationGroup b)) where
  K : ∀ a, Subgroup (source a)
  S : ∀ a, Finset (source a)
  generates : ∀ a,
    Subgroup.closure (((S a : Finset (source a)) : Set (source a)) ∪ K a) = ⊤
  generator_card : ∀ a, (S a).card ≤ l
  code : A → B × (Fin l → X)
  core_hom_card : ∀ a,
    Nat.card (K a →* Multiplicative (ZMod 4)) =
      Nat.card (target (code a).1 →* Multiplicative (ZMod 4))
  code_injective : Function.Injective code

namespace PermutationRelativeGeneratorEncoding

variable {b l : ℕ} {A B X : Type*} [Fintype A] [Fintype B] [Fintype X]
  {source : A → Subgroup (PermutationGroup b)}
  {target : B → Subgroup (PermutationGroup b)}

theorem fibre_card_le_one
    (E : PermutationRelativeGeneratorEncoding b l A B X source target)
    (z : B × (Fin l → X)) :
    Nat.card {a : A // E.code a = z} ≤ 1 := by
  rw [Finite.card_le_one_iff_subsingleton]
  exact ⟨fun x y =>
    Subtype.ext (E.code_injective (x.property.trans y.property.symm))⟩

/-- Joint marked transport through an unmarked relative-generator code. -/
theorem homMoment_sum_le
    (E : PermutationRelativeGeneratorEncoding b l A B X source target)
    (r : ℕ) :
    (∑ a : A,
        (Nat.card (source a →* Multiplicative (ZMod 4)) : ℝ) ^ r) ≤
      (Fintype.card X : ℝ) ^ l * (2 : ℝ) ^ (2 * r * l) *
        ∑ q : B,
          (Nat.card (target q →* Multiplicative (ZMod 4)) : ℝ) ^ r := by
  have hsum := homMoment_sum_le_of_relativeGenerator_encoding
    (fun a : A => source a) E.K E.S E.code
    (fun z : B × (Fin l → X) =>
      (Nat.card (target z.1 →* Multiplicative (ZMod 4)) : ℝ) ^ r)
    1 l r E.generates E.generator_card (fun _ => by positivity)
    (fun a => by
      rw [E.core_hom_card a]) E.fibre_card_le_one
  have hproduct :
      (∑ z : B × (Fin l → X),
          (Nat.card (target z.1 →* Multiplicative (ZMod 4)) : ℝ) ^ r) =
        (Fintype.card X : ℝ) ^ l *
          ∑ q : B,
            (Nat.card (target q →* Multiplicative (ZMod 4)) : ℝ) ^ r := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ q : B, ∑ _tuple : Fin l → X,
          (Nat.card (target q →* Multiplicative (ZMod 4)) : ℝ) ^ r) =
          ∑ q : B,
            (Fintype.card (Fin l → X) : ℝ) *
              (Nat.card (target q →* Multiplicative (ZMod 4)) : ℝ) ^ r := by
        apply Finset.sum_congr rfl
        intro q hq
        simp
      _ = (Fintype.card X : ℝ) ^ l *
          ∑ q : B,
            (Nat.card (target q →* Multiplicative (ZMod 4)) : ℝ) ^ r := by
        rw [← Finset.mul_sum]
        congr 1
        norm_cast
        rw [Fintype.card_fun, Fintype.card_fin]
  calc
    (∑ a : A,
        (Nat.card (source a →* Multiplicative (ZMod 4)) : ℝ) ^ r) ≤
      (1 : ℝ) * (2 : ℝ) ^ (2 * r * l) *
        ∑ z : B × (Fin l → X),
          (Nat.card (target z.1 →* Multiplicative (ZMod 4)) : ℝ) ^ r := by
      simpa only [Nat.cast_one] using hsum
    _ = (Fintype.card X : ℝ) ^ l * (2 : ℝ) ^ (2 * r * l) *
        ∑ q : B,
          (Nat.card (target q →* Multiplicative (ZMod 4)) : ℝ) ^ r := by
      rw [one_mul, hproduct]
      ring

end PermutationRelativeGeneratorEncoding

end MarkedC4
end SymmetricSubgroupAsymptotics

end
