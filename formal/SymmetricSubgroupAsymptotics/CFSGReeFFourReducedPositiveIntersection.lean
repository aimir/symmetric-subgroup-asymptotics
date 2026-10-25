import SymmetricSubgroupAsymptotics.CFSGReeFFourReducedSuffixSigns
import SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveWordIntersection
import SymmetricSubgroupAsymptotics.CFSGReeFFourShortMenuPeeling

/-! Exact full-intersection cardinality for every retained short relative
word. The literal terminal suffix signs, not a one-way cover, prove the
reverse inclusion into the counted recursive residual. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourReducedPositiveIntersection
open CFSGReeFFourReducedSuffixSigns CFSGReeFFourPositiveWordIntersection
open CFSGReeFFourShortMenuPeeling CFSGReeFFourShortPairedWeylMenu
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourInversionPeelingWords CFSGReeFFourFixedPositiveCardinality
open CFSGOpposedSubgroupPeelingChain CFSGOpposedSubgroupPeelingMembership

theorem positiveWordIntersection_eq_residual (m : ℕ) (head : Bool) (n : ℕ) (hn : n ≤ 8) :
    positiveWordIntersection m head n = residual (fixedPositive m) (step m head) n :=
  positiveWordIntersection_eq_residual_of_suffix_signs m head n
    (fun k hk a ha => reduced_suffix_positive n hn head k hk a ha)

theorem positiveWordIntersection_card_factorization
    (m : ℕ) (head : Bool) (n : ℕ) (hn : n ≤ 8) :
    Nat.card (fixedPositive m) = Nat.card (positiveWordIntersection m head n) *
      (2^(2*m+1))^(prefixWeight head n) :=
  positiveWordIntersection_card_factorization_of_suffix_signs m head n hn
    (fun k hk a ha => reduced_suffix_positive n hn head k hk a ha)

private theorem fullSuffix_eq_inversePrefix {G : Type*} [Group G]
    (w : ℕ → G) (n : ℕ) : inverseSuffix w n n = (wordPrefix w n)⁻¹ := by
  induction n with
  | zero => simp only [inverseSuffix, wordPrefix, inv_one]
  | succ n ih => rw [inverseSuffix, ih, wordPrefix, mul_inv_rev]

private theorem shortLength_le_eight (i : Fin 16) : shortLength i ≤ 8 := by
  simpa only [shortWord, List.length_map, List.length_range] using shortWord_length_le i

def shortPositiveIntersection (m : ℕ) (i : Fin 16) : Subgroup (originalModelFixed m) :=
  fixedPositive m ⊓ (fixedPositive m).comap (MulAut.conj (shortModelWord m i)).toMonoidHom

theorem shortPositiveIntersection_eq_residual (m : ℕ) (i : Fin 16) :
    shortPositiveIntersection m i = shortResidual m i := by
  have he : inverseSuffix (step m (shortHead i)) (shortLength i) (shortLength i) =
      shortModelWord m i := by
    rw [fullSuffix_eq_inversePrefix, short_prefix_eq_inverse, inv_inv]
  have h := positiveWordIntersection_eq_residual m (shortHead i) (shortLength i)
    (shortLength_le_eight i)
  simpa only [positiveWordIntersection, he, shortPositiveIntersection, shortResidual] using h

theorem shortPositiveIntersection_card_factorization (m : ℕ) (i : Fin 16) :
    Nat.card (fixedPositive m) = Nat.card (shortPositiveIntersection m i) *
      (2^(2*m+1))^(inversionWeight i) := by
  rw [shortPositiveIntersection_eq_residual]
  exact shortResidual_card_factorization m i

theorem shortPositiveIntersection_zero_card_le (i : Fin 16) (hi : 4 ≤ inversionWeight i) :
    Nat.card (shortPositiveIntersection 0 i) ≤ 256 := by
  have h := shortPositiveIntersection_card_factorization 0 i
  rw [fixedPositive_card] at h
  norm_num only [Nat.mul_zero, Nat.zero_add, pow_one] at h
  have hp : 16 ≤ 2^(inversionWeight i) :=
    (by decide : 16 = (2:ℕ)^4).le.trans (Nat.pow_le_pow_right (by decide) hi)
  have hm := Nat.mul_le_mul_left (Nat.card (shortPositiveIntersection 0 i)) hp
  rw [← h] at hm
  norm_num at hm
  omega

end SymmetricSubgroupAsymptotics.CFSGReeFFourReducedPositiveIntersection
