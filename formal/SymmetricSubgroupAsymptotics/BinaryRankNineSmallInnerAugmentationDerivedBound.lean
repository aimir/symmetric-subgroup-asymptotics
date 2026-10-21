import SymmetricSubgroupAsymptotics.BinaryEightAugmentationJointDimension
import SymmetricSubgroupAsymptotics.BinaryRankNineJointPairDerivedBounds

/-! A proved augmentation-head bound on the actual order32 inner top
implies derived order at most1024 for the same rank-nine original source. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (F : BinaryPairFrame U (Fin 16))
    (E : BinaryPairFrame F.top.range (Fin 8))
include F E

theorem rank_nine_derived_le_1024_of_inner_augmentation_head_one
    (hU : IsPGroup 2 U) (hrank : MarkedC4.genRank U = 9)
    (H : Subgroup (Equiv.Perm (Fin 8))) (hH : E.top.range = H)
    (hcard : Nat.card E.top.range = 32)
    (hmodel : ∀ A : Subrepresentation ((binaryPermutationRepresentation 8).comp H.subtype),
      A.toSubmodule = BinaryRegularEightNaturalRegistry.chart45.space →
      Module.finrank (ZMod 2) A.toRepresentation.Coinvariants ≤ 1)
    (hwide : 4 ≤ MarkedC4.normalGen F.top.ker) :
    Nat.card (commutator U) ≤ 1024 := by
  letI smallInnerAugmentationDerived_topTransitive : MulAction.IsPretransitive F.top.range (Fin 16) :=
    F.top_pretransitive
  let W := F.axisNaturalSubrepresentation F.top.ker
  have hW : 4 ≤ Module.finrank (ZMod 2) W.toRepresentation.Coinvariants := by
    rw [← F.axisNatural_normalGen F.top.ker le_rfl hU]
    exact hwide
  have hd := E.head_four_joint_dimension_le_fourteen_of_literal_augmentation_head
    (F.top_isPGroup hU) H hH hcard hmodel W hW
  have haxis : W.toSubmodule = F.kernelSpace := by
    apply le_antisymm (F.ambientAxis_le_kernelSpace F.top.ker)
    rintro v ⟨a, rfl⟩
    exact (F.bits_mem_ambientAxis F.top.ker a.toMul).mpr a.toMul.property
  rw [haxis] at hd
  exact F.rank_nine_derived_card_le_of_joint_pair_dimension E hU hrank 14 5 10
    (by omega) hcard.le (by decide)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
