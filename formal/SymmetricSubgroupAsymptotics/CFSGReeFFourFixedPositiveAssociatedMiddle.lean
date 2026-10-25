import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddlePositiveRemainderSupport
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleAssociatedQuotient
import SymmetricSubgroupAsymptotics.CFSGReeFFourSimpleBlockPeelingGeneration

/-! The checked SAME-group fixed sign factorization gives a genuinely
Ree-fixed middle factor after the strict outside-height remainder is
removed. The associated-graded image of the actual fixed positive group
is therefore covered by actual middle fixed parameters, without lifting
fixed points through a quotient or recognizing an abstract Levi group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveAssociatedMiddle
open CFSGReeFFourMiddlePositiveRemainderSupport CFSGReeFFourMiddleAssociatedQuotient
open CFSGReeFFourMiddleGradedKernel CFSGReeFFourFieldParameters
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourRelativePositiveSubgroups CFSGReeFFourFixedSubgroupPeeling
open CFSGReeFFourSimpleInversionBlocks CFSGReeFFourMiddleFixedInversion
open CFSGReeFFourMiddleFixedSubgroup CFSGReeFFourMiddleInversionCoverage
open CFSGReeFFourMiddleInversionSupport CFSGReeFFourRelativeWeylRawWords
open CFSGReeFFourFixedBruhatCover CFSGReeFFourRelativeSimpleWeyl
open CFSGFFourOriginalMiddleWords CFSGNormTwoGeckIntegralWord
open CFSGTwistedE6GeckPositiveTwist CFSGReeFFourMiddleParabolicFlag
open CFSGGradedMatrixSubgroups CFSGGradedMatrixAssociatedUnitHom
open CFSGOpposedSubgroupPeeling
private instance : DecidableEq (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _

private theorem middleWeight_eq :
    middleWeight = CFSGReeFFourMiddlePositivePreserving.middleWeight := by
  funext i
  cases i with
  | inl i => exact (map_zero CFSGE6GeckMiddleRootSupport.outsideHeight).symm
  | inr k => rfl

private theorem paired_middle_eq (m : ℕ) :
    fixedPairedWord m [true] = middleFixedWeyl m := by
  apply Subtype.ext
  simpa only [if_true] using single_paired_word_val m true

theorem fixedPositive_remainder_strict (m : ℕ) (p : originalModelFixed m)
    (hp : p ∈ fixedPositive m)
    (hwp : middleFixedWeyl m * p * (middleFixedWeyl m)⁻¹ ∈ fixedPositive m) :
    fixedRawHom m p ∈ strictUnits middleWeight := by
  rw [middleWeight_eq]
  have hn := hwp
  change rawHom (Field m) (middleRelativeWeyl m * p.val * (middleRelativeWeyl m)⁻¹) ∈
    Positive (Field m) at hn
  rw [map_mul,map_mul,map_inv,rawHom_middleRelativeWeyl] at hn
  apply middle_positive_remainder_le_strict (Field m)
  refine ⟨hp, ?_⟩
  simpa only [blockWord,word_eq_canonicalWord] using hn

theorem exists_fixed_strict_middle_factor (m : ℕ) (u : originalModelFixed m)
    (hu : u ∈ fixedPositive m) :
    ∃ p ∈ fixedPositive m, ∃ b ∈ middleFixedSubgroup m,
      u = p*b ∧ fixedRawHom m p ∈ strictUnits middleWeight := by
  obtain ⟨p,hp,b,hb,he,hwp⟩ := fixed_sign_factorization m [true] u hu
  have hblock : inversionPart (fixedPositive m) (CFSGReeFFourOppositionFixedPositiveNegative.fixedNegative m)
      (fixedPairedWord m [true]) = middleFixedSubgroup m :=
    (simple_inversion_eq_block m true).trans (fixedMiddleInversion_eq_middleFixedSubgroup m)
  rw [hblock] at hb
  rw [paired_middle_eq] at hwp
  exact ⟨p,hp,b,hb,he,fixedPositive_remainder_strict m p hp hwp⟩

theorem middleFixed_raw_preserving (m : ℕ) (b : originalModelFixed m)
    (hb : b ∈ middleFixedSubgroup m) : fixedRawHom m b ∈ preservingUnits middleWeight := by
  rw [middleWeight_eq]
  have hi : b ∈ fixedMiddleInversion m := by
    rw [fixedMiddleInversion_eq_middleFixedSubgroup]
    exact hb
  exact middleInversion_le_preserving (Field m) (rawHom_mem_middleInversion m b.val hi)

theorem exists_middle_associated_value (m : ℕ) (u : middleParabolic m)
    (hu : u.val ∈ fixedPositive m) :
    ∃ b : middleFixedSubgroup m, middleAssociatedHom m u = fixedRawHom m b.val := by
  obtain ⟨p,hp,b,hb,he,hs⟩ := exists_fixed_strict_middle_factor m u.val hu
  let P : middleParabolic m := ⟨p,positive_le_parabolic m hp⟩
  let B : middleParabolic m := ⟨b,positive_le_parabolic m
    (middleFixedSubgroup_le_fixedPositive m hb)⟩
  have huPB : u = P*B := Subtype.ext he
  have hPk : P ∈ (middleAssociatedHom m).ker := by
    rw [middleAssociatedHom_ker]
    exact hs
  have hP : middleAssociatedHom m P = 1 := hPk
  refine ⟨⟨b,hb⟩, ?_⟩
  rw [huPB,map_mul,hP,one_mul]
  exact associatedUnit_eq_of_preserving middleWeight (parabolicToTriangular m B)
    (middleFixed_raw_preserving m b hb)

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveAssociatedMiddle
