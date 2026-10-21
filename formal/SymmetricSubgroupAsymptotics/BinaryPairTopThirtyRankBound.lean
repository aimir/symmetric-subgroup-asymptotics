import SymmetricSubgroupAsymptotics.BinaryEightTop30NaturalHead
import SymmetricSubgroupAsymptotics.BinaryPairLiteralTopModel
import SymmetricSubgroupAsymptotics.BinaryPairRankFiveResidualTop
import SymmetricSubgroupAsymptotics.MarkedC4ActualGlobalMarkGeneratorRank

/-! The original30 action cannot be the pair-label top of a rank-five
source. The correlated original kernel is an actual submodule of the
checked natural representation, and the displayed top has three generators. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8))

theorem genRank_le_four_of_top_thirty (hU : IsPGroup 2 U)
    (hH : F.top.range = BinaryEightTop30CoordinateAction.H) :
    MarkedC4.genRank U ≤ 4 := by
  let W := F.literalTopAxis BinaryEightTop30CoordinateAction.H hH F.top.ker
  have hw := BinaryEightTop30NaturalHead.head_le_one W
  have hk : MarkedC4.normalGen F.top.ker ≤ 1 := by
    rw [F.axis_normalGen_eq_coinvariants F.top.ker le_rfl hU]
    change Module.finrank (ZMod 2)
      (F.literalTopAxis BinaryEightTop30CoordinateAction.H hH F.top.ker).toRepresentation.Coinvariants ≤ 1 at hw
    rw [F.literalTopAxis_head] at hw
    exact hw
  have hmodel : MarkedC4.genRank BinaryEightTop30CoordinateAction.H ≤ 3 := by
    let a := BinaryEightTop30CoordinateAction.generators
    let S : Finset BinaryEightTop30CoordinateAction.H := Finset.univ.image a
    have hs : (S : Set BinaryEightTop30CoordinateAction.H) = Set.range a := by
      ext x
      simp only [S,Finset.coe_image,Finset.coe_univ,Set.image_univ]
    have hg : Subgroup.closure (S : Set BinaryEightTop30CoordinateAction.H) = ⊤ := by
      rw [hs]
      exact BinaryEightTop30CoordinateAction.generators_full
    exact (MarkedC4.genRank_le hg).trans (Finset.card_image_le.trans (by simp))
  have ht := MarkedC4.ActualGlobalMarkGeneratorRank.genRank_le_of_surjective
    (MulEquiv.subgroupCongr hH).symm.toMonoidHom (MulEquiv.subgroupCongr hH).symm.surjective
  have hb := F.genRank_le_actual_pair_kernel_add_top
  omega
end SymmetricSubgroupAsymptotics.BinaryPairFrame
