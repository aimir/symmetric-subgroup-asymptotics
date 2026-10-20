import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalPresentation
import SymmetricSubgroupAsymptotics.PGroupNormalGeneratorCharacterEquality
import SymmetricSubgroupAsymptotics.MarkedC4ActualExcessOneQuotientRank

/-! Once the full original abelianization is proved to have exponent p,
its order is exactly p to the original generator rank. This is used only
after the actual square-carry obstruction has ruled out higher cyclic
factors; no elementary-abelianization hypothesis is silently inserted in
an order bound. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics

variable {G : Type} [Group G] (p : ℕ) [Fact p.Prime]

/-- Exponent p in the full original abelianization kills precisely the
power part of the whole-group relative radical. -/
theorem primeRelativeRadical_top_eq_commutator_of_abelianization_exponent
    (hexp : ∀ a : Abelianization G, a ^ p = 1) :
    primeRelativeRadical p (⊤ : Subgroup G) = commutator G := by
  rw [primeRelativeRadical_eq_powerCommutator, primeRelativePowerCommutator,
    ← commutator_def]
  apply sup_eq_right.mpr
  apply (Subgroup.closure_le (commutator G)).mpr
  rintro _ ⟨g, rfl⟩
  rw [← Abelianization.ker_of]
  change Abelianization.of ((g : G) ^ p) = 1
  rw [map_pow]
  exact hexp _

/-- This order identity concerns the full abelianization, after its
exponent has been established. -/
theorem pGroup_abelianization_card_eq_pow_normalGen_top [Finite G]
    (hG : IsPGroup p G) (hexp : ∀ a : Abelianization G, a ^ p = 1) :
    Nat.card (Abelianization G) = p ^ MarkedC4.normalGen (⊤ : Subgroup G) := by
  have hR := primeRelativeRadical_top_eq_commutator_of_abelianization_exponent p hexp
  have hfactor := primeRelativeRadical_card_factorization p (⊤ : Subgroup G)
  rw [← pGroup_normalGen_eq_primeRelativeHead p hG, hR, Subgroup.card_top] at hfactor
  have hwhole := Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator G)
  have hpos : 0 < Nat.card (commutator G) := Nat.card_pos
  change Nat.card G = Nat.card (Abelianization G) * Nat.card (commutator G) at hwhole
  nlinarith

/-- For a finite p-group the same identity uses ordinary generation. -/
theorem pGroup_abelianization_card_eq_pow_genRank [Finite G]
    (hG : IsPGroup p G) (hexp : ∀ a : Abelianization G, a ^ p = 1) :
    Nat.card (Abelianization G) = p ^ MarkedC4.genRank G := by
  letI : Group.IsNilpotent G := hG.isNilpotent
  rw [pGroup_abelianization_card_eq_pow_normalGen_top p hG hexp,
    MarkedC4.ActualExcessOneQuotientRank.normalGen_top_eq_genRank]

end SymmetricSubgroupAsymptotics
