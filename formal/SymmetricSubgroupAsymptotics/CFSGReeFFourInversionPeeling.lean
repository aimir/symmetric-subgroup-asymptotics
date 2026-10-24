import SymmetricSubgroupAsymptotics.CFSGReeFFourInversionPeelingWords
import SymmetricSubgroupAsymptotics.CFSGReeFFourInversionSuffixSigns
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedBlockConjugation

/-! Every actual simple inversion block is contained in its recursive
residual for the first eight alternating peels. This discharges the
geometric premise of the generic peeling theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourInversionPeeling
open CFSGOpposedSubgroupPeeling CFSGOpposedSubgroupPeelingChain
open CFSGOpposedSubgroupPeelingMembership CFSGReeFFourInversionPeelingWords
open CFSGReeFFourInversionSuffixSigns CFSGReeFFourInversionSuffixSignPilot
open CFSGReeFFourFixedBlockConjugation CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourSimpleInversionBlocks
open CFSGReeFFourFixedBruhatCover CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourOuterFixedInversion CFSGReeFFourMiddleFixedInversion

theorem simple_block_le_residual (m : ℕ) (head : Bool) (j : Fin 8) :
    inversionPart (fixedPositive m) (fixedNegative m) (step m head j.val) ≤
      residual (fixedPositive m) (step m head) j.val := by
  apply le_residual_of_inverse_suffixes
  intro x hx k hk
  have hk8 : k<8 := Nat.lt_of_le_of_lt hk j.isLt
  have hg := fixedRawHom_inverseSuffix m head j.val k
  rw [suffixWord_eq_profile head j ⟨k,hk8⟩ hk] at hg
  change x∈inversionPart (fixedPositive m) (fixedNegative m)
    (fixedPairedWord m [axis head j.val]) at hx
  rw [simple_inversion_eq_block] at hx
  cases haxis : axis head j.val
  · have hxb : x∈fixedOuterInversion m := by
      simpa only [haxis,Bool.false_eq_true,if_false] using hx
    rw [haxis] at hg
    have hmap := outer_block_conjugate_le m (inverseSuffix (step m head) j.val k)
      (conjugatingWord false k) hg (positiveBlockSigns_all_suffixes false ⟨k,hk8⟩)
    exact hmap ⟨x,hxb,rfl⟩
  · have hxb : x∈fixedMiddleInversion m := by
      simpa only [haxis,if_true] using hx
    rw [haxis] at hg
    have hmap := middle_block_conjugate_le m (inverseSuffix (step m head) j.val k)
      (conjugatingWord true k) hg (positiveBlockSigns_all_suffixes true ⟨k,hk8⟩)
    exact hmap ⟨x,hxb,rfl⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourInversionPeeling
