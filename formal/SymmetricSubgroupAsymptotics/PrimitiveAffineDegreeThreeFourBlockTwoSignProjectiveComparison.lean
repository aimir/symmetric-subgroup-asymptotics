import SymmetricSubgroupAsymptotics.CentralBinaryRecursiveCompleteQuotientComparison
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignProjectiveSeries

/-!
# Recursive QStar comparison for the literal two-sign projective series

When the actual four-point projective top is the dihedral group of order
eight, the order-four projective kernel is handled by its two central binary
factors.  The first central quotient maps onto `D8` with central kernel at
most two.  Its product with `C2` maps onto `D8 × C2` with the same kernel.
The recursive comparison therefore controls the original signed quotient
using exactly the three displayed quotients of `QStar`:

`D8`, `D8 × C2`, and `(D8 × C2) × C2`.

All maps below are the actual projective and quotient maps.  The only input
to this file is an identification of the already constructed literal
four-point top with `D8`; the order-four top is handled by one more use of
the recursive theorem in the subsequent top-recognition layer.
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

/-- The signed quotient before removing either projective-kernel factor. -/
abbrev DegreeThreeFourBlockTwoSignSignedQuotient :=
  preE7NonPairAction w U ⧸ E block P

/-- The first actual central quotient of the signed quotient. -/
abbrev DegreeThreeFourBlockTwoSignFirstCentralQuotient
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (PairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2) :=
  DegreeThreeFourBlockTwoSignSignedQuotient block P ⧸
    DegreeThreeFourBlockTwoSignCentralAxis
      block P hr hs hcomponent hbinary htwo

/-- The actual map after the first central quotient, with the literal
four-point top relabelled as `D8`. -/
def degreeThreeFourBlockTwoSign_projectiveD8AfterCentralAxis
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (PairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (topEquiv : DegreeThreeFourBlockTwoSignProjectiveImage
      block P hr hs hcomponent ≃* DegreeSixS3Wreath.D8) :
    DegreeThreeFourBlockTwoSignFirstCentralQuotient
        block P hr hs hcomponent hbinary htwo →*
      DegreeSixS3Wreath.D8 :=
  topEquiv.toMonoidHom.comp
    (degreeThreeFourBlockTwoSign_projectiveMapAfterCentralAxis
      block P hr hs hcomponent hbinary htwo)

theorem degreeThreeFourBlockTwoSign_projectiveD8AfterCentralAxis_surjective
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (PairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (topEquiv : DegreeThreeFourBlockTwoSignProjectiveImage
      block P hr hs hcomponent ≃* DegreeSixS3Wreath.D8) :
    Function.Surjective
      (degreeThreeFourBlockTwoSign_projectiveD8AfterCentralAxis
        block P hr hs hcomponent hbinary htwo topEquiv) :=
  topEquiv.surjective.comp
    (degreeThreeFourBlockTwoSign_projectiveMapAfterCentralAxis_surjective
      block P hr hs hcomponent hbinary htwo)

private theorem degreeThreeFourBlockTwoSign_projectiveD8AfterCentralAxis_ker
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (PairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (topEquiv : DegreeThreeFourBlockTwoSignProjectiveImage
      block P hr hs hcomponent ≃* DegreeSixS3Wreath.D8) :
    (degreeThreeFourBlockTwoSign_projectiveD8AfterCentralAxis
      block P hr hs hcomponent hbinary htwo topEquiv).ker =
    (degreeThreeFourBlockTwoSign_projectiveMapAfterCentralAxis
      block P hr hs hcomponent hbinary htwo).ker := by
  ext z
  simp only [MonoidHom.mem_ker,
    degreeThreeFourBlockTwoSign_projectiveD8AfterCentralAxis,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  constructor
  · intro hz
    apply topEquiv.injective
    simpa only [map_one] using hz
  · intro hz
    rw [hz, map_one]

/-- The first actual central quotient is a central binary extension of
the relabelled `D8` top. -/
noncomputable def degreeThreeFourBlockTwoSign_firstCentralD8GlobalComparison
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (PairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (topEquiv : DegreeThreeFourBlockTwoSignProjectiveImage
      block P hr hs hcomponent ≃* DegreeSixS3Wreath.D8) :
    CentralBinaryGlobalComparison
      DegreeThreeFourBlockTwoSignComparator.QStarGroup
      (DegreeThreeFourBlockTwoSignFirstCentralQuotient
        block P hr hs hcomponent hbinary htwo)
      DegreeSixS3Wreath.D8 := by
  let pi := degreeThreeFourBlockTwoSign_projectiveD8AfterCentralAxis
    block P hr hs hcomponent hbinary htwo topEquiv
  have hker : pi.ker =
      (degreeThreeFourBlockTwoSign_projectiveMapAfterCentralAxis
        block P hr hs hcomponent hbinary htwo).ker :=
    degreeThreeFourBlockTwoSign_projectiveD8AfterCentralAxis_ker
      block P hr hs hcomponent hbinary htwo topEquiv
  exact DegreeThreeFourBlockTwoSignComparator.centralD8GlobalComparison
    pi
    (degreeThreeFourBlockTwoSign_projectiveD8AfterCentralAxis_surjective
      block P hr hs hcomponent hbinary htwo topEquiv)
    (by
      intro z hz x
      exact
        degreeThreeFourBlockTwoSign_projectiveMapAfterCentralAxis_central_kernel
          block P hr hs hcomponent hbinary htwo z (by rwa [← hker]) x)
    (by
      rw [hker]
      exact degreeThreeFourBlockTwoSign_projectiveMapAfterCentralAxis_kernel_card_le
        block P hr hs hcomponent hbinary htwo)

/-- Recursive comparison of the first central quotient with `QStar`. -/
noncomputable def degreeThreeFourBlockTwoSign_firstCentralD8Comparison
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (PairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (topEquiv : DegreeThreeFourBlockTwoSignProjectiveImage
      block P hr hs hcomponent ≃* DegreeSixS3Wreath.D8) :=
  CentralBinaryRecursiveComparison.ofGlobal
    (degreeThreeFourBlockTwoSign_firstCentralD8GlobalComparison
      block P hr hs hcomponent hbinary htwo topEquiv)

/-- The same actual projective map after adjoining one binary factor. -/
noncomputable def degreeThreeFourBlockTwoSign_firstCentralD8ProductComparison
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (PairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (topEquiv : DegreeThreeFourBlockTwoSignProjectiveImage
      block P hr hs hcomponent ≃* DegreeSixS3Wreath.D8) :
    CentralBinaryRecursiveComparison
      DegreeThreeFourBlockTwoSignComparator.QStarGroup
      (DegreeThreeFourBlockTwoSignFirstCentralQuotient
        block P hr hs hcomponent hbinary htwo × C2)
      (DegreeSixS3Wreath.D8 × C2) := by
  let D := degreeThreeFourBlockTwoSign_firstCentralD8Comparison
    block P hr hs hcomponent hbinary htwo topEquiv
  apply D.prodC2 1
  intro b J
  simpa only [Nat.cast_one, one_mul] using
    completeQuotientWeight_le_of_surjective
      DegreeThreeFourBlockTwoSignComparator.qStarToD8C2C2
      DegreeThreeFourBlockTwoSignComparator.qStarToD8C2C2_surjective J

/-- The quotient by the first central axis is the outer actual central
binary projection used to recover the original signed quotient. -/
noncomputable def degreeThreeFourBlockTwoSign_signedQuotientD8Comparison
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (PairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (topEquiv : DegreeThreeFourBlockTwoSignProjectiveImage
      block P hr hs hcomponent ≃* DegreeSixS3Wreath.D8) :
    CentralBinaryRecursiveComparison
      DegreeThreeFourBlockTwoSignComparator.QStarGroup
      (DegreeThreeFourBlockTwoSignSignedQuotient block P)
      (DegreeThreeFourBlockTwoSignFirstCentralQuotient
        block P hr hs hcomponent hbinary htwo) := by
  let S := degreeThreeFourBlockTwoSign_projectiveKernelCentralSeries
    block P hr hs hcomponent hbinary htwo
  let D := degreeThreeFourBlockTwoSign_firstCentralD8Comparison
    block P hr hs hcomponent hbinary htwo topEquiv
  let Dprod := degreeThreeFourBlockTwoSign_firstCentralD8ProductComparison
    block P hr hs hcomponent hbinary htwo topEquiv
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
order-eight projective-top branch. -/
theorem degreeThreeFourBlockTwoSign_signedQuotient_completeWeight_le_of_topEquivD8
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (PairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (topEquiv : DegreeThreeFourBlockTwoSignProjectiveImage
      block P hr hs hcomponent ≃* DegreeSixS3Wreath.D8)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight
        (R := DegreeThreeFourBlockTwoSignSignedQuotient block P) J ≤
      ((degreeThreeFourBlockTwoSign_signedQuotientD8Comparison
          block P hr hs hcomponent hbinary htwo topEquiv).coefficient : ℝ) *
        completeQuotientWeight
          (R := DegreeThreeFourBlockTwoSignComparator.QStar) J := by
  let D := degreeThreeFourBlockTwoSign_signedQuotientD8Comparison
    block P hr hs hcomponent hbinary htwo topEquiv
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

/-- A uniform coefficient bound for the order-eight projective-top branch.
The deliberately loose exponent leaves ample room in the final `2^384`
budget while avoiding any normal-subgroup count. -/
theorem degreeThreeFourBlockTwoSign_signedQuotientD8Coefficient_le
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (PairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (topEquiv : DegreeThreeFourBlockTwoSignProjectiveImage
      block P hr hs hcomponent ≃* DegreeSixS3Wreath.D8) :
    (degreeThreeFourBlockTwoSign_signedQuotientD8Comparison
      block P hr hs hcomponent hbinary htwo topEquiv).coefficient ≤
        2 ^ 111 := by
  let R := DegreeThreeFourBlockTwoSignSignedQuotient block P
  let A := DegreeThreeFourBlockTwoSignFirstCentralQuotient
    block P hr hs hcomponent hbinary htwo
  let D := degreeThreeFourBlockTwoSign_firstCentralD8Comparison
    block P hr hs hcomponent hbinary htwo topEquiv
  let Dprod := degreeThreeFourBlockTwoSign_firstCentralD8ProductComparison
    block P hr hs hcomponent hbinary htwo topEquiv
  let O := degreeThreeFourBlockTwoSign_signedQuotientD8Comparison
    block P hr hs hcomponent hbinary htwo topEquiv
  have hR : Nat.card R ≤ 32 := by
    rcases degreeThreeFourBlockTwoSign_signedQuotient_card_cases
      block P hr hs hcomponent hbinary htwo with h | h <;> rw [h] <;> norm_num
  have hA : Nat.card A ≤ 32 :=
    (Nat.card_le_card_of_surjective
      (QuotientGroup.mk'
        (DegreeThreeFourBlockTwoSignCentralAxis
          block P hr hs hcomponent hbinary htwo))
      (QuotientGroup.mk'_surjective
        (DegreeThreeFourBlockTwoSignCentralAxis
          block P hr hs hcomponent hbinary htwo))).trans hR
  have hD8 : Nat.card DegreeSixS3Wreath.D8 ≤ 8 := by
    rw [SemidirectProduct.card, Nat.card_prod]
    norm_num [C2, Nat.card_zmod]
  have hD8C2 : Nat.card (DegreeSixS3Wreath.D8 × C2) ≤ 16 := by
    rw [Nat.card_prod]
    have hC2 : Nat.card C2 = 2 := by norm_num [C2, Nat.card_zmod]
    rw [hC2]
    omega
  have hD : D.coefficient ≤ 2 ^ 34 := by
    apply D.coefficient_le_two_pow 5 8 0
    · exact hA
    · exact hD8
    · change 1 ≤ 2 ^ 0
      norm_num
    · change 1 ≤ 2 ^ 0
      norm_num
  have hAprod : Nat.card (A × C2) ≤ 64 := by
    rw [Nat.card_prod]
    have hC2 : Nat.card C2 = 2 := by norm_num [C2, Nat.card_zmod]
    rw [hC2]
    omega
  have hDprod : Dprod.coefficient ≤ 2 ^ 53 := by
    apply Dprod.coefficient_le_two_pow 6 16 0
    · exact hAprod
    · exact hD8C2
    · change 1 ≤ 2 ^ 0
      norm_num
    · change 1 ≤ 2 ^ 0
      norm_num
  apply O.coefficient_le_two_pow 5 32 53 hR hA
  · exact hD.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  · exact hDprod

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
