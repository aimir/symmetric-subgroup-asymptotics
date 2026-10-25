import SymmetricSubgroupAsymptotics.CFSGReeFFourThreeStepSuffixSigns
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveCardinality

/-! The selected three-step full positive intersection is the actual
recursive residual. The reverse containment uses full positive-part
root-sign monotonicity and the faithful original word action; the
one-way residual bound is never treated as equality without this proof. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourThreeStepPositiveIntersection
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinateWeylIntersectionFactor
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckIntegralWord
open CFSGReeFFourThreeStepSuffixSigns CFSGReeFFourInversionPeelingWords
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

def threeStepIntersection (m : ℕ) (head : Bool) : Subgroup (originalModelFixed m) :=
  fixedPositive m ⊓ (fixedPositive m).comap
    (MulAut.conj (inverseSuffix (step m head) 3 3)).toMonoidHom

theorem threeStepIntersection_eq_residual (m : ℕ) (head : Bool) :
    threeStepIntersection m head = residual (fixedPositive m) (step m head) 3 := by
  apply le_antisymm
  · apply le_residual_of_inverse_suffixes
    intro x hx k hk
    let u : PositiveGroup A hd hs hp ho (Field m) := ⟨fixedRawHom m x, hx.1⟩
    have hraw : fixedRawHom m
        (inverseSuffix (step m head) 3 3 * x *
          (inverseSuffix (step m head) 3 3)⁻¹) ∈ Positive (Field m) := hx.2
    rw [map_mul, map_mul, map_inv, fixedRawHom_inverseSuffix,
      word_eq_canonicalWord] at hraw
    have hu : u ∈ wordSignPart A hd hs hp ho (Field m) (suffixWord head 3 3) false := hraw
    have hv := three_step_positive_part_le (Field m) head ⟨k, by omega⟩ hu
    change fixedRawHom m
      (inverseSuffix (step m head) 3 k * x *
        (inverseSuffix (step m head) 3 k)⁻¹) ∈ Positive (Field m)
    rw [map_mul, map_mul, map_inv, fixedRawHom_inverseSuffix,
      word_eq_canonicalWord]
    exact hv
  · exact residual_le_fullIntersection (fixedPositive m) (step m head) 3

theorem threeStepIntersection_card_factorization (m : ℕ) (head : Bool) :
    Nat.card (fixedPositive m) = Nat.card (threeStepIntersection m head) *
      (2^(2*m+1))^(prefixWeight head 3) := by
  rw [threeStepIntersection_eq_residual]
  exact fixedPositive_card_factorization m head 3 (by decide)

theorem threeStepIntersection_zero_card_le (head : Bool) :
    Nat.card (threeStepIntersection 0 head) ≤ 256 := by
  have h := threeStepIntersection_card_factorization 0 head
  rw [fixedPositive_card] at h
  cases head <;> norm_num [prefixWeight, axis, Finset.sum_range_succ] at h <;> omega

end SymmetricSubgroupAsymptotics.CFSGReeFFourThreeStepPositiveIntersection
