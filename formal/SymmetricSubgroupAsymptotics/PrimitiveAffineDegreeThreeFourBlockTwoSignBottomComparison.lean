import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignBottomCentralSeries
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignSectionComparison

/-!
# Uniform QStar comparison for the rank-two bottom

The bottom complement action kernel is either trivial, making the original
group the ternary wreath comparator, or nontrivial, when the constructed
two-step central series feeds the generic `QStar` comparison.  Both cases
fit the same `2^200` coefficient reserved by the structural assembly.
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

/-- The complete quotient weight of a rank-two bottom is controlled by the
fixed degree-ten comparator. -/
theorem degreeThreeFourBlockTwoSignBottom_completeQuotientWeight_le
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := G) J ≤
      (2 ^ 200 : ℝ) *
        completeQuotientWeight
          (R := DegreeThreeFourBlockTwoSignComparator.QStar) J := by
  let pi := degreeThreeFourBlockTwoSignBottomWreathMap
    block P hr hs hcomponent hbinary htwo hfin
  let topMap := degreeThreeFourBlockTwoSignBottomComplementD8Map
    block P hr hs hcomponent hbinary htwo hfin
  by_cases htop : topMap.ker = ⊥
  · have hpi_injective : Function.Injective pi :=
      degreeThreeFourBlockTwoSignBottomWreathMap_injective_of_topKernel_eq_bot
        block P hr hs hcomponent hbinary htwo hfin htop
    have hpi_surjective : Function.Surjective pi :=
      degreeThreeFourBlockTwoSignBottomWreathMap_surjective
        block P hr hs hcomponent hbinary htwo hfin
    let e : G ≃* DegreeSixS3Wreath.G :=
      MulEquiv.ofBijective pi ⟨hpi_injective, hpi_surjective⟩
    let q : DegreeThreeFourBlockTwoSignComparator.QStarGroup →* G :=
      e.symm.toMonoidHom.comp
        DegreeThreeFourBlockTwoSignComparator.qStarToWreath
    have hq : Function.Surjective q :=
      e.symm.surjective.comp
        DegreeThreeFourBlockTwoSignComparator.qStarToWreath_surjective
    have hone : completeQuotientWeight (R := G) J ≤
        completeQuotientWeight
          (R := DegreeThreeFourBlockTwoSignComparator.QStar) J :=
      DegreeThreeFourBlockTwoSignComparator.completeQuotientWeight_le_qStar_of_surjective
        q hq J
    calc
      completeQuotientWeight (R := G) J ≤
          1 * completeQuotientWeight
            (R := DegreeThreeFourBlockTwoSignComparator.QStar) J := by
        simpa only [one_mul] using hone
      _ ≤ (2 ^ 200 : ℝ) * completeQuotientWeight
          (R := DegreeThreeFourBlockTwoSignComparator.QStar) J := by
        apply mul_le_mul_of_nonneg_right
        · norm_num
        · exact completeQuotientWeight_nonneg J
  · let S :=
      degreeThreeFourBlockTwoSignBottomWreathKernelCentralSeries
        block P hr hs hcomponent hbinary htwo hfin htop
    have hkernel : Nat.card pi.ker ≤ 4 :=
      degreeThreeFourBlockTwoSignBottomWreathMap_kernel_card_le_four
        block P hr hs hcomponent hbinary htwo hfin
    have hG : Nat.card G ≤ 2 ^ 9 :=
      (degreeThreeFourBlock_twoSign_rankTwo_order_le_two_eighty_eight
        block P hr hs hcomponent hbinary htwo hfin).trans (by norm_num)
    calc
      completeQuotientWeight (R := G) J ≤
          ((DegreeThreeFourBlockTwoSignComparator.centralSeriesWreathComparison
            pi
            (degreeThreeFourBlockTwoSignBottomWreathMap_surjective
              block P hr hs hcomponent hbinary htwo hfin)
            S hkernel).coefficient : ℝ) *
            completeQuotientWeight
              (R := DegreeThreeFourBlockTwoSignComparator.QStar) J :=
        DegreeThreeFourBlockTwoSignComparator.centralSeriesWreath_completeQuotientWeight_le
          pi
          (degreeThreeFourBlockTwoSignBottomWreathMap_surjective
            block P hr hs hcomponent hbinary htwo hfin)
          S hkernel J
      _ ≤ (2 ^ 200 : ℝ) * completeQuotientWeight
          (R := DegreeThreeFourBlockTwoSignComparator.QStar) J := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast
            DegreeThreeFourBlockTwoSignComparator.centralSeriesWreath_coefficient_le
              pi
              (degreeThreeFourBlockTwoSignBottomWreathMap_surjective
                block P hr hs hcomponent hbinary htwo hfin)
              S hkernel hG
        · exact completeQuotientWeight_nonneg J

/-- The rank-two bottom epimorphism count in the exact form expected by the
two-sign structural assembly. -/
theorem degreeThreeFourBlockTwoSignBottom_epimorphism_card_le
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J G) : ℝ) ≤
      (2 ^ 200 : ℝ) *
        completeQuotientWeight
          (R := DegreeThreeFourBlockTwoSignComparator.QStar) J := by
  let M : {N : Subgroup G // N.Normal} := ⟨⊥, inferInstance⟩
  have hbottom := card_groupEpimorphism_le_completeQuotientWeight J M
    (QuotientGroup.quotientBot (G := G)).symm
  exact hbottom.trans
    (degreeThreeFourBlockTwoSignBottom_completeQuotientWeight_le
      block P hr hs hcomponent hbinary htwo hfin J)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
