import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedSubgroupPeeling
import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterFixedInversion
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFixedInversion

/-! The actual single-letter opposed blocks have cardinal q and q².
Their first-peel identities retain the literal residual subgroup; no
eight-step positive-group count is inferred here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourSimpleInversionBlocks
open CFSGOpposedSubgroupPeeling CFSGReeFFourFixedSubgroupPeeling
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourOppositionFixedPositiveNegative
open CFSGReeFFourFixedBruhatCover CFSGReeFFourOriginalWeylWords
open CFSGReeFFourFixedWordClassification CFSGReeFFourPairedWordActions
open CFSGReeFFourRelativeSimpleWeyl CFSGReeFFourOriginalInversionFactors
open CFSGReeFFourOriginalNegativeStability CFSGFFourOriginalAmbientHom
open CFSGReeFFourOuterFixedInversion CFSGReeFFourMiddleFixedInversion

theorem single_paired_word_val (m : ℕ) (b : Bool) :
    (fixedPairedWord m [b]).val = if b then middleRelativeWeyl m else outerRelativeWeyl m := by
  cases b <;>
    simp only [fixedPairedWord,expandPaired,pairedRelativeWord,List.append_nil,
      Bool.false_eq_true,if_false,if_true,modelWeylWord,mul_one,
      outerRelativeWeyl,middleRelativeWeyl,mul_assoc]

theorem simple_inversion_eq_block (m : ℕ) (b : Bool) :
    inversionPart (fixedPositive m) (fixedNegative m) (fixedPairedWord m [b]) =
      if b then fixedMiddleInversion m else fixedOuterInversion m := by
  cases b
  · apply Subgroup.ext
    intro g
    change (g.val∈modelPositive (Field m) ∧
      (fixedPairedWord m [false]).val*g.val*(fixedPairedWord m [false]).val⁻¹∈modelNegative m) ↔
      g.val∈modelInversion m (outerRelativeWeyl m)
    rw [single_paired_word_val]
    rfl
  · apply Subgroup.ext
    intro g
    change (g.val∈modelPositive (Field m) ∧
      (fixedPairedWord m [true]).val*g.val*(fixedPairedWord m [true]).val⁻¹∈modelNegative m) ↔
      g.val∈modelInversion m (middleRelativeWeyl m)
    rw [single_paired_word_val]
    rfl

theorem simple_inversion_card (m : ℕ) (b : Bool) :
    Nat.card (inversionPart (fixedPositive m) (fixedNegative m) (fixedPairedWord m [b])) =
      (2^(2*m+1))^(if b then 2 else 1) := by
  cases b
  · rw [simple_inversion_eq_block]
    simpa only [Bool.false_eq_true,if_false,pow_one] using fixedOuterInversion_card m
  · rw [simple_inversion_eq_block]
    exact fixedMiddleInversion_card m

theorem fixedPositive_card_simple_peel (m : ℕ) (b : Bool) :
    Nat.card (fixedPositive m) =
      Nat.card (remainderPart (fixedPositive m) (fixedPositive m) (fixedPairedWord m [b])) *
        (2^(2*m+1))^(if b then 2 else 1) := by
  rw [←simple_inversion_card m b]
  exact fixedPositive_card_first_peel m [b]

end SymmetricSubgroupAsymptotics.CFSGReeFFourSimpleInversionBlocks
