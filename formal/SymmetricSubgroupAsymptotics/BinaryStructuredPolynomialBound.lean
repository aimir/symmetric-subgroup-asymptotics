import SymmetricSubgroupAsymptotics.BinaryStructuredEpiPolynomial

/-! Uniform polynomial losses for actual structured epimorphism counts.
The source-order bound concerns the same original source. A common bound
on the explicit target constants suffices for a fixed finite alphabet;
the center and derived slopes are not enlarged or discarded.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

theorem binaryCharacterRank_le_of_card_le_pow
    (G : Type*) [Group G] [Finite G] (s : ℕ)
    (hcard : Nat.card G ≤ 2^s) : binaryCharacterRank G ≤ s := by
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    ((primeCharacters_pow_finrank_le_card 2 G).trans hcard)

/-- A shared target constant bounds each polynomial loss, while the source
rank is bounded independently by its actual original order or degree. -/
theorem binaryStructured_polynomial_le_uniform
    (Q : Type*) [Group Q] [Finite Q] (d s C : ℕ)
    (hd : d ≤ s) (hC : binaryStructuredEpiConstant Q ≤ C) :
    binaryStructuredEpiConstant Q * (d+2)^(binaryStructuredEpiConstant Q) ≤
      C * (s+2)^C := by
  apply Nat.mul_le_mul hC
  calc
    _ ≤ (s+2)^(binaryStructuredEpiConstant Q) :=
      Nat.pow_le_pow_left (Nat.add_le_add_right hd 2) _
    _ ≤ _ := Nat.pow_le_pow_right (by omega) hC

/-- Uniform polynomial control leaves both proved exponential slopes on
the actual source unchanged. No source class or alphabet premise is needed. -/
theorem binaryStructured_epimorphism_card_le_uniform
    {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q]
    (hG : IsPGroup 2 G) (hQ : IsPGroup 2 Q) (s C : ℕ)
    (hcard : Nat.card G ≤ 2^s) (hC : binaryStructuredEpiConstant Q ≤ C) :
    Nat.card {f : G →* Q // Function.Surjective f} ≤
      C * (s+2)^C *
        2^(Nat.log 2 (Nat.card (Subgroup.center Q)) * binaryCharacterRank G +
          Nat.log 2 (Nat.card (commutator Q)) * primeDerivedNormalRank 2 G) := by
  exact (binaryStructured_epimorphism_card_le_polynomial hG hQ).trans
    (Nat.mul_le_mul_right _ (binaryStructured_polynomial_le_uniform Q _ s C
      (binaryCharacterRank_le_of_card_le_pow G s hcard) hC))

/-- All losses in one finite history share the same proved majorant.
This includes the empty history, whose product is one. -/
theorem binaryStructured_polynomial_prod_le_uniform
    {ι : Type*} (I : Finset ι) (Q : ι → Type*)
    [∀ i, Group (Q i)] [∀ i, Finite (Q i)] (d : ι → ℕ) (s C : ℕ)
    (hd : ∀ i ∈ I, d i ≤ s)
    (hC : ∀ i ∈ I, binaryStructuredEpiConstant (Q i) ≤ C) :
    (∏ i ∈ I, binaryStructuredEpiConstant (Q i) *
      (d i+2)^(binaryStructuredEpiConstant (Q i))) ≤
        (C*(s+2)^C)^I.card := by
  calc
    _ ≤ ∏ _i ∈ I, C*(s+2)^C :=
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i hi =>
        binaryStructured_polynomial_le_uniform (Q i) (d i) s C (hd i hi) (hC i hi))
    _ = _ := by simp

end SymmetricSubgroupAsymptotics
