import SymmetricSubgroupAsymptotics.BinaryElementaryActualComparatorSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTranslationDualUniform
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFixedCellOrders

/-! Complete original-normal-axis cold-rank data for actual affine16
translation cells. No solubility or published16 locator is needed. The
comparator remains the actual quotient, in its faithful8s-point action. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre) [Nontrivial block.Fibre]

/-- Stop at the actual correlated translation kernel and retain its
actual quotient as comparator; all maps and all original normals remain. -/
def sixteenTranslationColdData
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre=16) (m t : ℕ)
    (hG : Nat.card (preE7NonPairAction w U) ≤ 2^m)
    (hQ : Nat.card (preE7NonPairAction w U ⧸
      E block (sixteenBinaryProfile block P hr)) ≤ 2^t) :
    PreE7DegreeTwoPairSummedSource w U := by
  let Q := sixteenBinaryProfile block P hr
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block Q
  let pi := QuotientGroup.mk' (E block Q)
  let A := (ActualWreathAffineCapacity.E S (localMap block Q) C).quotientRepresentation
  let EC := ActualWreathAffineCapacity.originalChart S (localMap block Q) C
  have hu : UniformSubrepresentationGeneratorBound A.ρ.dual
      (2*Fintype.card block.Points) :=
    sixteen_translation_dual_uniform block P hTraceyPerm hr
  exact BinaryElementaryActualComparatorSource.data
    pi (QuotientGroup.mk'_surjective (E block Q)) A EC hu m t hG hQ
    (8*Fintype.card block.Points)
    (quotientSixteenEightAction block Q hr)
    (quotientSixteenEightAction_injective block Q hr)

/-- Actual two-block cell: coefficient2^2730, cold slope51/50,
comparator16, and fixed factorial-tail power39+2^31. -/
def sixteenTwoBlockColdData
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre=16) (hs : Nat.card block.Points=2) :
    PreE7DegreeTwoPairSummedSource w U :=
  let caps := sixteen_twoBlock_order_budgets block (sixteenBinaryProfile block P hr) hr hs
  sixteenTranslationColdData block P hTraceyPerm hr 39 31 caps.1 caps.2

/-- Actual four-block cell: coefficient2^11826, cold slope51/25,
comparator32, and fixed factorial-tail power81+2^65. -/
def sixteenFourBlockColdData
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre=16) (hs : Nat.card block.Points=4) :
    PreE7DegreeTwoPairSummedSource w U :=
  let caps := sixteen_fourBlock_order_budgets block (sixteenBinaryProfile block P hr) hr hs
  sixteenTranslationColdData block P hTraceyPerm hr 81 65 caps.1 caps.2

theorem sixteenTwoBlockColdData_eta
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre=16) (hs : Nat.card block.Points=2) :
    (sixteenTwoBlockColdData block P hTraceyPerm hr hs).eta=51/50 := by
  change (51/200 : ℝ)*((2*Fintype.card block.Points : ℕ) : ℝ)=51/50
  have hc : Fintype.card block.Points=2 := by simpa only [Fintype.card_eq_nat_card] using hs
  rw [hc]
  norm_num

theorem sixteenFourBlockColdData_eta
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre=16) (hs : Nat.card block.Points=4) :
    (sixteenFourBlockColdData block P hTraceyPerm hr hs).eta=51/25 := by
  change (51/200 : ℝ)*((2*Fintype.card block.Points : ℕ) : ℝ)=51/25
  have hc : Fintype.card block.Points=4 := by simpa only [Fintype.card_eq_nat_card] using hs
  rw [hc]
  norm_num

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
