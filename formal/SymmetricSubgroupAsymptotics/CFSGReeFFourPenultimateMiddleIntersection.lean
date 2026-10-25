import SymmetricSubgroupAsymptotics.CFSGReeFFourReducedPositiveIntersection
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryMiddleGenerators

/-! The OTHER length-seven position is the WHOLE literal middle block.
The existing last-peel inclusion and exact intersection count prove this
for all field parameters. At the binary parameter the block is cyclic
of order four. Intrinsic fixation of its Weyl representative is separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourPenultimateMiddleIntersection
open CFSGReeFFourReducedPositiveIntersection CFSGReeFFourShortMenuPeeling
open CFSGReeFFourInversionPeeling CFSGReeFFourInversionPeelingWords
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourShortPairedWeylMenu CFSGReeFFourSimpleInversionBlocks
open CFSGReeFFourFixedBruhatCover CFSGReeFFourMiddleFixedInversion
open CFSGReeFFourMiddleFixedSubgroup CFSGReeFFourFixedPositiveCardinality
open CFSGReeFFourFixedAmbientHom CFSGReeFFourBinaryMiddleGenerators
open CFSGReeFFourMiddleDerivedFiveWord CFSGOpposedSubgroupPeelingChain

private instance fixedFinite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)

private theorem cancel_ten (q c : ℕ) (hq : 0<q) (h : q^12=c*q^10) : c=q^2 := by
  have he : q^2*q^10=c*q^10 := (pow_add q 2 10).symm.trans h
  exact (Nat.eq_of_mul_eq_mul_right (pow_pos hq 10) he).symm

theorem middle_le_penultimate_intersection (m : ℕ) :
    middleFixedSubgroup m≤shortPositiveIntersection m (13 : Fin 16) := by
  rw [shortPositiveIntersection_eq_residual]
  change middleFixedSubgroup m≤residual (fixedPositive m) (step m false) 7
  have h := simple_block_le_residual m false (7 : Fin 8)
  change CFSGOpposedSubgroupPeeling.inversionPart (fixedPositive m)
    (CFSGReeFFourOppositionFixedPositiveNegative.fixedNegative m)
    (fixedPairedWord m [true])≤residual (fixedPositive m) (step m false) 7 at h
  rw [simple_inversion_eq_block] at h
  simpa only [if_true,fixedMiddleInversion_eq_middleFixedSubgroup] using h

theorem penultimate_intersection_card (m : ℕ) :
    Nat.card (shortPositiveIntersection m (13 : Fin 16))=(2^(2*m+1))^2 := by
  have h := shortPositiveIntersection_card_factorization m (13 : Fin 16)
  have hw : inversionWeight (13 : Fin 16)=10 := by decide +kernel
  rw [fixedPositive_card,hw] at h
  exact cancel_ten _ _ (pow_pos (by decide : 0<(2 : ℕ)) _) h

theorem penultimate_intersection_eq_middle (m : ℕ) :
    shortPositiveIntersection m (13 : Fin 16)=middleFixedSubgroup m := by
  apply (Subgroup.eq_of_le_of_card_ge (middle_le_penultimate_intersection m) ?_).symm
  rw [middleFixedSubgroup_card,penultimate_intersection_card]

theorem binary_penultimate_eq_zpowers :
    shortPositiveIntersection 0 (13 : Fin 16)=Subgroup.zpowers (fourCycle 0) :=
  (penultimate_intersection_eq_middle 0).trans middleFixed_zero_eq_zpowers

end SymmetricSubgroupAsymptotics.CFSGReeFFourPenultimateMiddleIntersection
