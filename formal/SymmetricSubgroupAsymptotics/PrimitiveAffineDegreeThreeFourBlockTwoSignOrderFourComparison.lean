import SymmetricSubgroupAsymptotics.OrderFourCentralBinaryRecursiveComparison
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignProjectiveComparison

/-!
# The order-four projective branch of the two-sign comparison

This file binds the generic order-four central-binary recursion to the
actual signed quotient and its two projective-kernel factors.  The
construction treats cyclic and Klein-four projective tops identically:
both first descend through a chosen central order-two axis to `C₂`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

private abbrev C2 := Multiplicative (ZMod 2)

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

private abbrev PairChart
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6) :=
  degreeThreeFourBlockPairChart block P hr hs hcomponent

/-- The first projective central quotient, compared recursively through an
arbitrary actual projective top of order four. -/
noncomputable def degreeThreeFourBlockTwoSign_firstCentralOrderFourComparison
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (PairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (htop : Nat.card (DegreeThreeFourBlockTwoSignProjectiveImage
      block P hr hs hcomponent) = 4) :
    CentralBinaryRecursiveComparison
      DegreeThreeFourBlockTwoSignComparator.QStarGroup
      (DegreeThreeFourBlockTwoSignFirstCentralQuotient
        block P hr hs hcomponent hbinary htwo)
      (DegreeThreeFourBlockTwoSignProjectiveImage
        block P hr hs hcomponent) := by
  let A := DegreeThreeFourBlockTwoSignProjectiveImage
    block P hr hs hcomponent
  let D := OrderFourCentralBinaryRecursiveComparison.comparison A htop
  let Dprod :=
    OrderFourCentralBinaryRecursiveComparison.productComparison A htop
  refine
    { projection := degreeThreeFourBlockTwoSign_projectiveMapAfterCentralAxis
        block P hr hs hcomponent hbinary htwo
      projection_surjective :=
        degreeThreeFourBlockTwoSign_projectiveMapAfterCentralAxis_surjective
          block P hr hs hcomponent hbinary htwo
      central_kernel :=
        degreeThreeFourBlockTwoSign_projectiveMapAfterCentralAxis_central_kernel
          block P hr hs hcomponent hbinary htwo
      kernel_card_le_two :=
        degreeThreeFourBlockTwoSign_projectiveMapAfterCentralAxis_kernel_card_le
          block P hr hs hcomponent hbinary htwo
      baseCoefficient := D.coefficient
      productCoefficient := Dprod.coefficient
      base_complete_bound := D.completeQuotientWeight_le
      product_complete_bound := Dprod.completeQuotientWeight_le }

/-- The same actual first projective quotient after adjoining one binary
factor.  The rank-four elementary quotient of `QStar` supplies the last
recursive input. -/
noncomputable def degreeThreeFourBlockTwoSign_firstCentralOrderFourProductComparison
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (PairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (htop : Nat.card (DegreeThreeFourBlockTwoSignProjectiveImage
      block P hr hs hcomponent) = 4) :
    CentralBinaryRecursiveComparison
      DegreeThreeFourBlockTwoSignComparator.QStarGroup
      (DegreeThreeFourBlockTwoSignFirstCentralQuotient
        block P hr hs hcomponent hbinary htwo × C2)
      (DegreeThreeFourBlockTwoSignProjectiveImage
        block P hr hs hcomponent × C2) := by
  let A := DegreeThreeFourBlockTwoSignProjectiveImage
    block P hr hs hcomponent
  let D := degreeThreeFourBlockTwoSign_firstCentralOrderFourComparison
    block P hr hs hcomponent hbinary htwo htop
  let Ddouble :=
    OrderFourCentralBinaryRecursiveComparison.doubleProductComparison A htop
  apply D.prodC2 Ddouble.coefficient
  exact Ddouble.completeQuotientWeight_le

/-- Complete recursive comparison for the actual signed quotient when its
literal projective top has order four. -/
noncomputable def degreeThreeFourBlockTwoSign_signedQuotientOrderFourComparison
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (PairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (htop : Nat.card (DegreeThreeFourBlockTwoSignProjectiveImage
      block P hr hs hcomponent) = 4) :
    CentralBinaryRecursiveComparison
      DegreeThreeFourBlockTwoSignComparator.QStarGroup
      (DegreeThreeFourBlockTwoSignSignedQuotient block P)
      (DegreeThreeFourBlockTwoSignFirstCentralQuotient
        block P hr hs hcomponent hbinary htwo) := by
  let S := degreeThreeFourBlockTwoSign_projectiveKernelCentralSeries
    block P hr hs hcomponent hbinary htwo
  let D := degreeThreeFourBlockTwoSign_firstCentralOrderFourComparison
    block P hr hs hcomponent hbinary htwo htop
  let Dprod :=
    degreeThreeFourBlockTwoSign_firstCentralOrderFourProductComparison
      block P hr hs hcomponent hbinary htwo htop
  refine
    { projection := QuotientGroup.mk' S.C
      projection_surjective := QuotientGroup.mk'_surjective S.C
      central_kernel := ?_
      kernel_card_le_two := ?_
      baseCoefficient := D.coefficient
      productCoefficient := Dprod.coefficient
      base_complete_bound := D.completeQuotientWeight_le
      product_complete_bound := Dprod.completeQuotientWeight_le }
  · intro z hz x
    have hzC : z ∈ S.C := by
      simpa only [QuotientGroup.ker_mk'] using hz
    exact (Subgroup.mem_center_iff.mp (S.C_le_center hzC) x).symm
  · rw [QuotientGroup.ker_mk', S.C_card]

/-- Complete `QStar` comparison for the actual signed quotient in the
order-four projective-top branch. -/
theorem degreeThreeFourBlockTwoSign_signedQuotient_completeWeight_le_of_top_card_four
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (PairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (htop : Nat.card (DegreeThreeFourBlockTwoSignProjectiveImage
      block P hr hs hcomponent) = 4)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight
        (R := DegreeThreeFourBlockTwoSignSignedQuotient block P) J ≤
      ((degreeThreeFourBlockTwoSign_signedQuotientOrderFourComparison
          block P hr hs hcomponent hbinary htwo htop).coefficient : ℝ) *
        completeQuotientWeight
          (R := DegreeThreeFourBlockTwoSignComparator.QStar) J := by
  let D := degreeThreeFourBlockTwoSign_signedQuotientOrderFourComparison
    block P hr hs hcomponent hbinary htwo htop
  calc
    completeQuotientWeight
        (R := DegreeThreeFourBlockTwoSignSignedQuotient block P) J ≤
      (D.coefficient : ℝ) * completeQuotientWeight
        (R := DegreeThreeFourBlockTwoSignComparator.QStarGroup) J :=
          D.completeQuotientWeight_le J
    _ = (D.coefficient : ℝ) * completeQuotientWeight
        (R := DegreeThreeFourBlockTwoSignComparator.QStar) J := by
      rw [Non2UnipotentPrefixFiniteMenu.completeQuotientWeight_congr
        DegreeThreeFourBlockTwoSignComparator.qStarEquiv J]

/-- Uniform numerical coefficient in the order-four projective-top branch. -/
theorem degreeThreeFourBlockTwoSign_signedQuotientOrderFourCoefficient_le
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (PairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (htop : Nat.card (DegreeThreeFourBlockTwoSignProjectiveImage
      block P hr hs hcomponent) = 4) :
    (degreeThreeFourBlockTwoSign_signedQuotientOrderFourComparison
      block P hr hs hcomponent hbinary htwo htop).coefficient ≤
        2 ^ 128 := by
  let R := DegreeThreeFourBlockTwoSignSignedQuotient block P
  let X := DegreeThreeFourBlockTwoSignFirstCentralQuotient
    block P hr hs hcomponent hbinary htwo
  let A := DegreeThreeFourBlockTwoSignProjectiveImage
    block P hr hs hcomponent
  let T := OrderFourCentralBinaryRecursiveComparison.comparison A htop
  let Tprod :=
    OrderFourCentralBinaryRecursiveComparison.productComparison A htop
  let Tdouble :=
    OrderFourCentralBinaryRecursiveComparison.doubleProductComparison A htop
  let D := degreeThreeFourBlockTwoSign_firstCentralOrderFourComparison
    block P hr hs hcomponent hbinary htwo htop
  let Dprod :=
    degreeThreeFourBlockTwoSign_firstCentralOrderFourProductComparison
      block P hr hs hcomponent hbinary htwo htop
  let O := degreeThreeFourBlockTwoSign_signedQuotientOrderFourComparison
    block P hr hs hcomponent hbinary htwo htop
  have hR : Nat.card R ≤ 32 := by
    rcases degreeThreeFourBlockTwoSign_signedQuotient_card_cases
      block P hr hs hcomponent hbinary htwo with h | h <;> rw [h] <;> norm_num
  have hX : Nat.card X ≤ 32 :=
    (Nat.card_le_card_of_surjective
      (QuotientGroup.mk'
        (DegreeThreeFourBlockTwoSignCentralAxis
          block P hr hs hcomponent hbinary htwo))
      (QuotientGroup.mk'_surjective
        (DegreeThreeFourBlockTwoSignCentralAxis
          block P hr hs hcomponent hbinary htwo))).trans hR
  have hT : T.coefficient ≤ 2 ^ 7 :=
    OrderFourCentralBinaryRecursiveComparison.comparison_coefficient_le A htop
  have hTprod : Tprod.coefficient ≤ 2 ^ 14 :=
    OrderFourCentralBinaryRecursiveComparison.productComparison_coefficient_le
      A htop
  have hTdouble : Tdouble.coefficient ≤ 2 ^ 25 :=
    OrderFourCentralBinaryRecursiveComparison.doubleProductComparison_coefficient_le
      A htop
  have hD : D.coefficient ≤ 2 ^ 44 := by
    apply D.coefficient_le_two_pow 5 4 14
    · exact hX
    · exact htop.le
    · change T.coefficient ≤ 2 ^ 14
      exact hT.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    · change Tprod.coefficient ≤ 2 ^ 14
      exact hTprod
  have hXprod : Nat.card (X × C2) ≤ 64 := by
    rw [Nat.card_prod]
    have hC2 : Nat.card C2 = 2 := by norm_num [C2, Nat.card_zmod]
    rw [hC2]
    omega
  have hAprod : Nat.card (A × C2) ≤ 8 := by
    rw [Nat.card_prod, htop]
    norm_num [C2, Nat.card_zmod]
  have hDprod : Dprod.coefficient ≤ 2 ^ 70 := by
    apply Dprod.coefficient_le_two_pow 6 8 25
    · exact hXprod
    · exact hAprod
    · change Tprod.coefficient ≤ 2 ^ 25
      exact hTprod.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    · change Tdouble.coefficient ≤ 2 ^ 25
      exact hTdouble
  apply O.coefficient_le_two_pow 5 32 70 hR hX
  · change D.coefficient ≤ 2 ^ 70
    exact hD.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  · change Dprod.coefficient ≤ 2 ^ 70
    exact hDprod

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
