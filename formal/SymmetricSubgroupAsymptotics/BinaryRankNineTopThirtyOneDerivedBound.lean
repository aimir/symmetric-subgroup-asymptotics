import SymmetricSubgroupAsymptotics.BinaryPairLargeTopWideActualBounds
import SymmetricSubgroupAsymptotics.BinaryRankNineJointPairDerivedBounds

/-! The same original rank-nine source above the literal31 inner top
has derived order at most1024. Its two actual outer layers have combined
dimension ten and its actual inner kernel is the three-space chart44. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (F : BinaryPairFrame U (Fin 16))
    (E : BinaryPairFrame F.top.range (Fin 8))
include F E

theorem rank_nine_top_thirty_one_inner_derived_card_le_1024
    (hU : IsPGroup 2 U) (hrank : MarkedC4.genRank U = 9)
    (hTopRank : 5 ≤ MarkedC4.genRank F.top.range)
    (hH : E.top.range = BinaryEightTop31CoordinateAction.H)
    (hwide : 4 ≤ MarkedC4.normalGen F.top.ker) :
    Nat.card (commutator U) ≤ 1024 := by
  letI topThirtyOneDerived_topTransitive : MulAction.IsPretransitive F.top.range (Fin 16) :=
    F.top_pretransitive
  let W := F.axisNaturalSubrepresentation F.top.ker
  have hW : 4 ≤ Module.finrank (ZMod 2) W.toRepresentation.Coinvariants := by
    rw [← F.axisNatural_normalGen F.top.ker le_rfl hU]
    exact hwide
  have hd := E.naturalModule_finrank_le_ten_of_top_thirty_one_rank_five_head_four
    (F.top_isPGroup hU) hTopRank hH W hW
  have hJ := E.kernelSpace_eq_chart44_of_top_thirty_one_rank_five_head_four
    (F.top_isPGroup hU) hTopRank hH W hW
  have hJdim : Module.finrank (ZMod 2) E.kernelSpace = 3 := by
    rw [hJ, BinaryRegularEightNaturalRegistry.chart44.finrank]
  have haxis : W.toSubmodule = F.kernelSpace := by
    apply le_antisymm (F.ambientAxis_le_kernelSpace F.top.ker)
    rintro v ⟨a, rfl⟩
    exact (F.bits_mem_ambientAxis F.top.ker a.toMul).mpr a.toMul.property
  rw [haxis] at hd
  have hHcard : Nat.card E.top.range = 64 :=
    (Nat.card_congr (MulEquiv.subgroupCongr hH).toEquiv).trans BinaryMenuCayley8T31.exact_card
  exact F.rank_nine_derived_card_le_of_joint_pair_dimension E hU hrank 13 6 10
    (by omega) hHcard.le (by decide)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
