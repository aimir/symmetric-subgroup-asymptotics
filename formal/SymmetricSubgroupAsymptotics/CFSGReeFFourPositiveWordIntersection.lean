import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylPositivePartMonotonicity
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveCardinality

/-! The full positive intersection is the actual recursive residual
whenever the literal reduced suffixes retain every surviving positive root. The reverse containment uses full positive-part
root-sign monotonicity and the faithful original word action; the
one-way residual bound is never treated as equality without this proof. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveWordIntersection
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinateWeylIntersectionFactor
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckIntegralWord
open CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGNormTwoCoordinateWeylPositivePartMonotonicity CFSGReeFFourInversionPeelingWords
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFixedPositiveCardinality
open CFSGOpposedSubgroupPeelingChain CFSGOpposedSubgroupPeelingMembership
open CFSGTwistedE6GeckPositiveTwist
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local instance : DecidableEq (Roots A) := Classical.decEq _

private theorem fullSuffix_eq_inversePrefix {G : Type*} [Group G]
    (w : ℕ → G) (n : ℕ) : inverseSuffix w n n = (wordPrefix w n)⁻¹ := by
  induction n with
  | zero => simp only [inverseSuffix, wordPrefix, inv_one]
  | succ n ih => rw [inverseSuffix, ih, wordPrefix, mul_inv_rev]

private theorem residual_le_fullIntersection {G : Type*} [Group G]
    (U : Subgroup G) (w : ℕ → G) (n : ℕ) :
    residual U w n ≤ U ⊓ U.comap (MulAut.conj (inverseSuffix w n n)).toMonoidHom := by
  intro x hx
  refine ⟨residual_le U w n hx, ?_⟩
  obtain ⟨y, hy, he⟩ := residual_le_prefix U w n hx
  change wordPrefix w n * y * (wordPrefix w n)⁻¹ = x at he
  change inverseSuffix w n n * x * (inverseSuffix w n n)⁻¹ ∈ U
  rw [fullSuffix_eq_inversePrefix]
  have heq : (wordPrefix w n)⁻¹ * x * ((wordPrefix w n)⁻¹)⁻¹ = y := by
    rw [← he]
    group
  rw [heq]
  exact hy

def positiveWordIntersection (m : ℕ) (head : Bool) (n : ℕ) :
    Subgroup (originalModelFixed m) :=
  fixedPositive m ⊓ (fixedPositive m).comap
    (MulAut.conj (inverseSuffix (step m head) n n)).toMonoidHom

theorem positiveWordIntersection_eq_residual_of_suffix_signs
    (m : ℕ) (head : Bool) (n : ℕ)
    (hroot : ∀ k ≤ n, ∀ a : PositiveRoot A,
      (∀ j, 0 ≤ (wordRoot A hs hp (coordinateBase A hd hs hp ho)
        (coordinateIndexEquiv A hd hs hp ho) (suffixWord head n n) a.val).val j) →
      ∀ j, 0 ≤ (wordRoot A hs hp (coordinateBase A hd hs hp ho)
        (coordinateIndexEquiv A hd hs hp ho) (suffixWord head n k) a.val).val j) :
    positiveWordIntersection m head n = residual (fixedPositive m) (step m head) n := by
  apply le_antisymm
  · apply le_residual_of_inverse_suffixes
    intro x hx k hk
    let u : PositiveGroup A hd hs hp ho (Field m) := ⟨fixedRawHom m x, hx.1⟩
    have hraw : fixedRawHom m
        (inverseSuffix (step m head) n n * x *
          (inverseSuffix (step m head) n n)⁻¹) ∈ Positive (Field m) := hx.2
    rw [map_mul, map_mul, map_inv, fixedRawHom_inverseSuffix,
      word_eq_canonicalWord] at hraw
    have hu : u ∈ wordSignPart A hd hs hp ho (Field m) (suffixWord head n n) false := hraw
    have hv := positive_part_le_of_root_implication A hd hs hp ho (Field m)
      (suffixWord head n n) (suffixWord head n k) (hroot k hk) hu
    change fixedRawHom m
      (inverseSuffix (step m head) n k * x *
        (inverseSuffix (step m head) n k)⁻¹) ∈ Positive (Field m)
    rw [map_mul, map_mul, map_inv, fixedRawHom_inverseSuffix,
      word_eq_canonicalWord]
    exact hv
  · exact residual_le_fullIntersection (fixedPositive m) (step m head) n

theorem positiveWordIntersection_card_factorization_of_suffix_signs
    (m : ℕ) (head : Bool) (n : ℕ) (hn : n ≤ 8)
    (hroot : ∀ k ≤ n, ∀ a : PositiveRoot A,
      (∀ j, 0 ≤ (wordRoot A hs hp (coordinateBase A hd hs hp ho)
        (coordinateIndexEquiv A hd hs hp ho) (suffixWord head n n) a.val).val j) →
      ∀ j, 0 ≤ (wordRoot A hs hp (coordinateBase A hd hs hp ho)
        (coordinateIndexEquiv A hd hs hp ho) (suffixWord head n k) a.val).val j) :
    Nat.card (fixedPositive m) = Nat.card (positiveWordIntersection m head n) *
      (2^(2*m+1))^(prefixWeight head n) := by
  rw [positiveWordIntersection_eq_residual_of_suffix_signs m head n hroot]
  exact fixedPositive_card_factorization m head n hn

end SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveWordIntersection
