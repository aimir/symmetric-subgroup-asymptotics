import SymmetricSubgroupAsymptotics.BinaryStructuredPolynomialBound

/-! A common structured-counting constant from the actual target order.
One bound on the carrier orders controls all of their normal quotients.
The exponential center and derived slopes retain their original values.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- A deliberately coarse explicit constant depending only on the order cap. -/
def binaryStructuredOrderConstant (a : ℕ) : ℕ :=
  max a ((2^a)^((2^a)^a))

theorem binaryStructuredOrderConstant_pos (a : ℕ) :
    0 < binaryStructuredOrderConstant a :=
  lt_of_lt_of_le (pow_pos (pow_pos (by decide : 0 < (2 : ℕ)) _) _)
    (le_max_right _ _)

theorem binaryStructuredEpiConstant_le_orderConstant
    (Q : Type*) [Group Q] [Finite Q] (a : ℕ)
    (hcard : Nat.card Q ≤ 2^a) :
    binaryStructuredEpiConstant Q ≤ binaryStructuredOrderConstant a := by
  have hlog : Nat.log 2 (Nat.card Q) ≤ a := by
    simpa only [Nat.log_pow (by decide : 1 < 2)] using
      (Nat.log_mono_right (b := 2) hcard)
  have hderived : Nat.card (commutator Q) ≤ 2^a :=
    (Nat.card_le_card_of_injective (commutator Q).subtype Subtype.val_injective).trans
      hcard
  have hexp : (Nat.card (commutator Q))^(Nat.log 2 (Nat.card Q)) ≤ (2^a)^a :=
    (Nat.pow_le_pow_left hderived _).trans
      (Nat.pow_le_pow_right (pow_pos (by decide : 0 < (2 : ℕ)) _) hlog)
  have hpow : (Nat.card Q)^((Nat.card (commutator Q))^(Nat.log 2 (Nat.card Q))) ≤
      (2^a)^((2^a)^a) :=
    (Nat.pow_le_pow_left hcard _).trans
      (Nat.pow_le_pow_right (pow_pos (by decide : 0 < (2 : ℕ)) _) hexp)
  exact max_le_max hlog hpow

/-- Every literal normal quotient inherits the same constant. -/
theorem binaryStructuredQuotientConstant_le_orderConstant
    (A : Type*) [Group A] [Finite A] (N : Subgroup A) [N.Normal]
    (a : ℕ) (hcard : Nat.card A ≤ 2^a) :
    binaryStructuredEpiConstant (A ⧸ N) ≤ binaryStructuredOrderConstant a := by
  apply binaryStructuredEpiConstant_le_orderConstant
  exact (Nat.card_le_card_of_surjective (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N)).trans hcard

/-- Both the source and target constants now follow from actual order bounds. -/
theorem binaryStructured_epimorphism_card_le_order_uniform
    {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q]
    (hG : IsPGroup 2 G) (hQ : IsPGroup 2 Q) (s a : ℕ)
    (hGcard : Nat.card G ≤ 2^s) (hQcard : Nat.card Q ≤ 2^a) :
    Nat.card {f : G →* Q // Function.Surjective f} ≤
      binaryStructuredOrderConstant a * (s+2)^(binaryStructuredOrderConstant a) *
        2^(Nat.log 2 (Nat.card (Subgroup.center Q)) * binaryCharacterRank G +
          Nat.log 2 (Nat.card (commutator Q)) * primeDerivedNormalRank 2 G) :=
  binaryStructured_epimorphism_card_le_uniform hG hQ s _ hGcard
    (binaryStructuredEpiConstant_le_orderConstant Q a hQcard)

end SymmetricSubgroupAsymptotics
