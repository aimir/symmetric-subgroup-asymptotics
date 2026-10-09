import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignSectionCentralSeries
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignTernarySectionComparison
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignStructural

/-!
# Uniform QStar comparison for every proper two-sign section

The complement action kernel is either trivial, in which case the section
is the literal ternary wreath comparator, or nontrivial, in which case the
central series constructed in the preceding file feeds the generic
two-step comparison.  Both cases satisfy the same `2^200` bound.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

private abbrev G := preE7NonPairAction w U

/-- Every literal proper section is controlled by `QStar` with the uniform
coefficient reserved in the two-sign structural assembly. -/
theorem degreeThreeFourBlockTwoSignSection_completeQuotientWeight_le
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P))
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight
        (R := G ⧸ degreeThreeFourBlockTwoSignSectionAxis block P N) J ≤
      (2 ^ 200 : ℝ) *
        completeQuotientWeight
          (R := DegreeThreeFourBlockTwoSignComparator.QStar) J := by
  let R := G ⧸ degreeThreeFourBlockTwoSignSectionAxis block P N
  let pi := degreeThreeFourBlockTwoSignSectionWreathMap
    block P hr hs hcomponent hbinary htwo N
  let topMap := degreeThreeFourBlockTwoSignSectionComplementD8Map
    block P hr hs hcomponent hbinary htwo N
  by_cases htop : topMap.ker = ⊥
  · have hpi_injective : Function.Injective pi :=
      degreeThreeFourBlockTwoSignSectionWreathMap_injective_of_topKernel_eq_bot
        block P hr hs hcomponent hbinary htwo N htop
    have hpi_surjective : Function.Surjective pi :=
      degreeThreeFourBlockTwoSignSectionWreathMap_surjective
        block P hr hs hcomponent hbinary htwo N
    let e : R ≃* DegreeSixS3Wreath.G :=
      MulEquiv.ofBijective pi ⟨hpi_injective, hpi_surjective⟩
    let q : DegreeThreeFourBlockTwoSignComparator.QStarGroup →* R :=
      e.symm.toMonoidHom.comp
        DegreeThreeFourBlockTwoSignComparator.qStarToWreath
    have hq : Function.Surjective q :=
      e.symm.surjective.comp
        DegreeThreeFourBlockTwoSignComparator.qStarToWreath_surjective
    have hone : completeQuotientWeight (R := R) J ≤
        completeQuotientWeight
          (R := DegreeThreeFourBlockTwoSignComparator.QStar) J :=
      DegreeThreeFourBlockTwoSignComparator.completeQuotientWeight_le_qStar_of_surjective
        q hq J
    calc
      completeQuotientWeight (R := R) J ≤
          1 * completeQuotientWeight
            (R := DegreeThreeFourBlockTwoSignComparator.QStar) J := by
        simpa only [one_mul] using hone
      _ ≤ (2 ^ 200 : ℝ) * completeQuotientWeight
          (R := DegreeThreeFourBlockTwoSignComparator.QStar) J := by
        apply mul_le_mul_of_nonneg_right
        · norm_num
        · exact completeQuotientWeight_nonneg J
  · let S :=
      degreeThreeFourBlockTwoSignSectionWreathKernelCentralSeries
        block P hr hs hcomponent hbinary htwo N htop
    have hkernel : Nat.card pi.ker ≤ 4 :=
      degreeThreeFourBlockTwoSignSectionWreathMap_kernel_card_le_four
        block P hr hs hcomponent hbinary htwo N
    have hR : Nat.card R ≤ 2 ^ 9 :=
      (degreeThreeFourBlockTwoSignSectionQuotient_card_le_two_eighty_eight
        block P hr hs hcomponent hbinary htwo N).trans (by norm_num)
    calc
      completeQuotientWeight (R := R) J ≤
          ((DegreeThreeFourBlockTwoSignComparator.centralSeriesWreathComparison
            pi
            (degreeThreeFourBlockTwoSignSectionWreathMap_surjective
              block P hr hs hcomponent hbinary htwo N)
            S hkernel).coefficient : ℝ) *
            completeQuotientWeight
              (R := DegreeThreeFourBlockTwoSignComparator.QStar) J :=
        DegreeThreeFourBlockTwoSignComparator.centralSeriesWreath_completeQuotientWeight_le
          pi
          (degreeThreeFourBlockTwoSignSectionWreathMap_surjective
            block P hr hs hcomponent hbinary htwo N)
          S hkernel J
      _ ≤ (2 ^ 200 : ℝ) * completeQuotientWeight
          (R := DegreeThreeFourBlockTwoSignComparator.QStar) J := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast
            DegreeThreeFourBlockTwoSignComparator.centralSeriesWreath_coefficient_le
              pi
              (degreeThreeFourBlockTwoSignSectionWreathMap_surjective
                block P hr hs hcomponent hbinary htwo N)
              S hkernel hR
        · exact completeQuotientWeight_nonneg J

/-- The preceding comparison in the bundled form expected by the literal
normal-axis stratification. -/
theorem degreeThreeFourBlockTwoSignSection_bundledWeight_le
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P))
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    bundledNormalQuotientWeight (twoSignProperAxis N) J ≤
      (2 ^ 200 : ℝ) *
        completeQuotientWeight
          (R := DegreeThreeFourBlockTwoSignComparator.QStar) J := by
  change completeQuotientWeight
      (R := G ⧸ degreeThreeFourBlockTwoSignSectionAxis block P N) J ≤ _
  exact degreeThreeFourBlockTwoSignSection_completeQuotientWeight_le
    block P hr hs hcomponent hbinary htwo N J

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
