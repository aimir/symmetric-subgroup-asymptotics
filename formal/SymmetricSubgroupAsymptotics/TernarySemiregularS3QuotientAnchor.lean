import SymmetricSubgroupAsymptotics.BinaryBySymmetricThreeSocle
import SymmetricSubgroupAsymptotics.TernaryOddPartNonbinaryCentralRank

/-!
# Nonbinary quotient anchors from the original ternary geometry

Let the original group act faithfully on 24 points, have order `2^a * 3`,
and have every nonidentity cubic element act without fixed points. Assume
an actual surjection from that original group to `S₃` has binary kernel.
Every displayed nonbinary quotient then has a four-generator socle and
one ordinary plus three relative character slots.

Central binary rank four is proved by the original Sylow-centralizer orbit
argument. The quotient's exact odd part is derived from its order dividing
the original order and from nonbinaryity. No central-rank, multiplicity,
module-census, or character-feasibility premise is added. The only character
theorem input is the existing published whole-socle Zmud statement.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- A nonbinary divisor of an order with one odd factor has that same
odd factor exactly once. The binary exponent can only decrease. -/
theorem ternaryOddPart_exists_card_eq_of_not_isPGroup_two
    {Q : Type*} [Group Q] [Finite Q] {a : ℕ}
    (hdiv : Nat.card Q ∣ 2 ^ a * 3) (hQ : ¬ IsPGroup 2 Q) :
    ∃ b ≤ a, Nat.card Q = 2 ^ b * 3 := by
  have hthree := ternaryOddPart_three_dvd_card_of_not_isPGroup_two hdiv hQ
  obtain ⟨m, hm⟩ := hthree
  have hmul : 3 * m ∣ 3 * 2 ^ a := by
    simpa only [hm, Nat.mul_comm] using hdiv
  have hmdiv : m ∣ 2 ^ a :=
    Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 3) hmul
  obtain ⟨b, hba, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hmdiv
  refine ⟨b, hba, ?_⟩
  rw [hm, hb, Nat.mul_comm]

/-- The centralizer geometry and the Schur section argument combine on
the same original quotient map to give four socle normal generators. -/
theorem ternarySemiregular_s3_nonbinary_quotient_socleGeneratorBound
    {G X Q : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] [Group Q] [Finite Q] {a : ℕ}
    (hX : Nat.card X = 24) (hcard : Nat.card G = 2 ^ a * 3)
    (hfree : ∀ g : G, g ^ 3 = 1 → g ≠ 1 → ∀ x : X, g • x ≠ x)
    (beta : G →* Equiv.Perm (Fin 3)) (hbeta : Function.Surjective beta)
    (hker : IsPGroup 2 beta.ker)
    (pi : G →* Q) (hpi : Function.Surjective pi) (hQ : ¬ IsPGroup 2 Q) :
    SocleNormalGeneratorBound Q 4 := by
  have hcentral := ternaryOddPart_nonbinary_quotient_central_finrank_le_four
    hX hcard hfree pi hpi hQ
  have hdiv : Nat.card Q ∣ 2 ^ a * 3 := by
    simpa only [hcard] using Subgroup.card_dvd_of_surjective pi hpi
  exact socleNormalGeneratorBound_four_of_original_binary_kernel_symmetricThree
    pi hpi hX beta hbeta hker hcentral hdiv

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

/-- The actual nonbinary quotient has profile `(0,0,1,3)`. Both the
central rank and the exact retained odd-part formula are proved here. -/
noncomputable def ternarySemiregular_s3_nonbinary_quotient_anchor
    (hZmud : ZmudFaithfulCharacterTupleInput)
    {G X Q : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] [Group Q] [Finite Q] {a : ℕ}
    (hX : Nat.card X = 24) (hcard : Nat.card G = 2 ^ a * 3)
    (hfree : ∀ g : G, g ^ 3 = 1 → g ≠ 1 → ∀ x : X, g • x ≠ x)
    (beta : G →* Equiv.Perm (Fin 3)) (hbeta : Function.Surjective beta)
    (hker : IsPGroup 2 beta.ker)
    (pi : G →* Q) (hpi : Function.Surjective pi) (hQ : ¬ IsPGroup 2 Q) :
    DegreeTwoPairRelativeKernelAnchor Q (degreeTwoPairOrdinaryRelativeProfile 1 3) := by
  have hcentral := ternaryOddPart_nonbinary_quotient_central_finrank_le_four
    hX hcard hfree pi hpi hQ
  have hdiv : Nat.card Q ∣ 2 ^ a * 3 := by
    simpa only [hcard] using Subgroup.card_dvd_of_surjective pi hpi
  let orderData := ternaryOddPart_exists_card_eq_of_not_isPGroup_two hdiv hQ
  exact ordinaryRelativeAnchor_of_original_binary_kernel_symmetricThree
    hZmud pi hpi hX beta hbeta hker hcentral orderData.choose_spec.2

/-- Normal-subgroup form: the retained quotient is literally `G/N`. -/
noncomputable def ternarySemiregular_s3_nonbinary_normal_quotient_anchor
    (hZmud : ZmudFaithfulCharacterTupleInput)
    {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] {a : ℕ}
    (hX : Nat.card X = 24) (hcard : Nat.card G = 2 ^ a * 3)
    (hfree : ∀ g : G, g ^ 3 = 1 → g ≠ 1 → ∀ x : X, g • x ≠ x)
    (beta : G →* Equiv.Perm (Fin 3)) (hbeta : Function.Surjective beta)
    (hker : IsPGroup 2 beta.ker)
    (N : Subgroup G) [N.Normal] (hQ : ¬ IsPGroup 2 (G ⧸ N)) :
    DegreeTwoPairRelativeKernelAnchor (G ⧸ N)
      (degreeTwoPairOrdinaryRelativeProfile 1 3) :=
  ternarySemiregular_s3_nonbinary_quotient_anchor hZmud hX hcard hfree
    beta hbeta hker (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hQ

end SymmetricSubgroupAsymptotics

end
