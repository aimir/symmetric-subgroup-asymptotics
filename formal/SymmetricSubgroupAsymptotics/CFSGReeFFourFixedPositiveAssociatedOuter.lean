import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterPositiveRemainderSupport
import SymmetricSubgroupAsymptotics.CFSGReeFFourSimpleBlockPeelingGeneration
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckArbitraryHeightSupport

/-! The SAME original Ree-fixed sign factorization leaves an actual
outer fixed parameter after removing the strict inside-height remainder.
Thus the associated image of the actual positive group is covered by
actual outer parameters, with no fixed-quotient lifting premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveAssociatedOuter
open CFSGReeFFourOuterPositiveRemainderSupport CFSGReeFFourOuterGradedQuotient
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourRelativePositiveSubgroups
open CFSGReeFFourFixedSubgroupPeeling CFSGReeFFourSimpleBlockPeelingGeneration
open CFSGReeFFourOuterFixedRoot CFSGReeFFourRelativeWeylRawWords
open CFSGReeFFourFixedBruhatCover CFSGReeFFourMinimalParabolics
open CFSGReeFFourRelativeSimpleWeyl CFSGFFourOriginalMiddleWords
open CFSGNormTwoGeckIntegralWord CFSGTwistedE6GeckPositiveTwist
open CFSGReeFFourOuterParabolicFlag CFSGGradedMatrixSubgroups
open CFSGGradedMatrixAssociatedUnitHom CFSGNormTwoGeckArbitraryHeightSupport
open CFSGTwistedE6GeckDiagramCovariance CFSGSerreQuadraticMatrix
open CFSGFFourE6FixedGeneratedGroup
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
private instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

theorem positive_le_parabolic (m : ℕ) : fixedPositive m ≤ outerParabolic m :=
  (show fixedPositive m ≤ fixedPositive m ⊔ fixedDiagonal m from le_sup_left).trans le_sup_left

theorem fixedPositive_remainder_strict (m : ℕ) (p : originalModelFixed m)
    (hpositive : p ∈ fixedPositive m)
    (hwp : outerFixedWeyl m * p * (outerFixedWeyl m)⁻¹ ∈ fixedPositive m) :
    fixedRawHom m p ∈ strictUnits outerWeight := by
  have hn := hwp
  change rawHom (Field m) (outerRelativeWeyl m * p.val * (outerRelativeWeyl m)⁻¹) ∈
    Positive (Field m) at hn
  rw [map_mul, map_mul, map_inv, rawHom_outerRelativeWeyl] at hn
  apply outer_positive_remainder_le_strict (Field m)
  refine ⟨hpositive, ?_⟩
  simpa only [CFSGReeFFourOuterInversionRoots.blockWord, word_eq_canonicalWord] using hn

theorem exists_fixed_strict_outer_factor (m : ℕ) (u : originalModelFixed m)
    (hu : u ∈ fixedPositive m) :
    ∃ p ∈ fixedPositive m, ∃ b ∈ (fixedOuterHom m).range,
      u = p*b ∧ fixedRawHom m p ∈ strictUnits outerWeight := by
  obtain ⟨p, hpositive, b, hb, he, hwp⟩ := fixed_sign_factorization m [false] u hu
  change b ∈ CFSGOpposedSubgroupPeeling.inversionPart (fixedPositive m)
    (CFSGReeFFourOppositionFixedPositiveNegative.fixedNegative m) (simpleWeyl m false) at hb
  rw [outer_simple_inversion_eq] at hb
  change fixedPairedWord m [false] * p * (fixedPairedWord m [false])⁻¹ ∈ fixedPositive m at hwp
  change simpleWeyl m false * p * (simpleWeyl m false)⁻¹ ∈ fixedPositive m at hwp
  rw [simpleWeyl_false] at hwp
  exact ⟨p, hpositive, b, hb, he, fixedPositive_remainder_strict m p hpositive hwp⟩

theorem fixedOuter_raw_preserving (m : ℕ) (a : Multiplicative (Field m)) :
    fixedRawHom m (fixedOuterHom m a) ∈ preservingUnits outerWeight := by
  change rawHom (Field m) (outerWord m a.toAdd) ∈ preservingUnits outerWeight
  simp only [outerWord, map_mul, rawHom_root, folded_root_eq_orbitParameter]
  change (canonicalRoot rawData (Field m) false 0 a.toAdd *
      canonicalRoot rawData (Field m) false 5 a.toAdd) *
    canonicalRoot rawData (Field m) false 1 (alpha m a.toAdd) ∈ _
  apply (preservingUnits outerWeight).mul_mem
  · apply (preservingUnits outerWeight).mul_mem
    · exact canonicalRoot_preserves A hs hp E6Base E6Index insideHeight (Field m) 0 a.toAdd rfl
    · exact canonicalRoot_preserves A hs hp E6Base E6Index insideHeight (Field m) 5 a.toAdd rfl
  · exact canonicalRoot_preserves A hs hp E6Base E6Index insideHeight (Field m) 1 (alpha m a.toAdd) rfl

theorem exists_outer_associated_value (m : ℕ) (u : outerParabolic m)
    (hu : u.val ∈ fixedPositive m) :
    ∃ a : Multiplicative (Field m), outerAssociatedHom m u = fixedRawHom m (fixedOuterHom m a) := by
  obtain ⟨p, hpositive, b, hb, he, hstrict⟩ := exists_fixed_strict_outer_factor m u.val hu
  obtain ⟨a, rfl⟩ := hb
  let P : outerParabolic m := ⟨p, positive_le_parabolic m hpositive⟩
  let B : outerParabolic m := ⟨fixedOuterHom m a, positive_le_parabolic m
    (fixedOuterHom_range_le_fixedPositive m ⟨a, rfl⟩)⟩
  have huPB : u = P*B := Subtype.ext he
  have hPk : P ∈ (outerAssociatedHom m).ker := by
    rw [outerAssociatedHom_ker]
    exact hstrict
  have hP : outerAssociatedHom m P = 1 := hPk
  refine ⟨a, ?_⟩
  rw [huPB, map_mul, hP, one_mul]
  exact associatedUnit_eq_of_preserving outerWeight (parabolicToTriangular m B)
    (fixedOuter_raw_preserving m a)

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveAssociatedOuter
