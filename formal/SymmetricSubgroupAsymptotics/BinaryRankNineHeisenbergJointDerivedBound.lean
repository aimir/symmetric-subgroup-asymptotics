import SymmetricSubgroupAsymptotics.BinaryHeisenbergJointWideLayerDimension
import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerJointDimension
import SymmetricSubgroupAsymptotics.BinaryPairRankFiveKernelConstant
import SymmetricSubgroupAsymptotics.BinaryRankNineJointPairDerivedBounds
import SymmetricSubgroupAsymptotics.BinaryPairLiteralTopModel

/-! The original rank-nine source above an actual Heisenberg eight-point
inner top has derived order at most1024. No source splitting is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (F : BinaryPairFrame U (Fin 16))
    (E : BinaryPairFrame F.top.range (Fin 8))
include F E

theorem rank_nine_heisenberg_inner_top_derived_card_le_1024
    (hU : IsPGroup 2 U) (hrank : MarkedC4.genRank U = 9)
    (hTopRank : 5 ≤ MarkedC4.genRank F.top.range)
    (hH : E.top.range = BinaryHeisenbergEightNaturalHeads.H)
    (hwide : 4 ≤ MarkedC4.normalGen F.top.ker) :
    Nat.card (commutator U) ≤ 1024 := by
  letI heisenbergJointDerived_topTransitive : MulAction.IsPretransitive F.top.range (Fin 16) :=
    F.top_pretransitive
  let W := F.axisNaturalSubrepresentation F.top.ker
  have hW : 4 ≤ Module.finrank (ZMod 2) W.toRepresentation.Coinvariants := by
    rw [← F.axisNatural_normalGen F.top.ker le_rfl hU]
    exact hwide
  let K := E.literalTopKernel BinaryHeisenbergEightNaturalHeads.H hH
  have hK : E.kernelSpace = K.toSubmodule :=
    (E.literalTopKernel_space BinaryHeisenbergEightNaturalHeads.H hH).symm
  have hconstant : (1 : Fin 8 → ZMod 2) ∈ K.toSubmodule := by
    rw [← hK]
    exact E.rank_five_kernelSpace_contains_one (F.top_isPGroup hU) hTopRank
  have hd := E.naturalModule_kernel_add_finrank_le_of_literal_joint_profile
    BinaryHeisenbergEightNaturalHeads.H hH K hK 4 14
    (fun S L hp hh => BinaryHeisenbergEightNaturalHeads.head_four_joint_layer_dimension_le_fourteen
      K S L hconstant hp hh) W hW
  have haxis : W.toSubmodule = F.kernelSpace := by
    apply le_antisymm (F.ambientAxis_le_kernelSpace F.top.ker)
    rintro v ⟨a, rfl⟩
    exact (F.bits_mem_ambientAxis F.top.ker a.toMul).mpr a.toMul.property
  rw [haxis] at hd
  have hHcard : Nat.card E.top.range = 32 :=
    (Nat.card_congr (MulEquiv.subgroupCongr hH).toEquiv).trans BinaryMenuCayley8T22.exact_card
  exact F.rank_nine_derived_card_le_of_joint_pair_dimension E hU hrank 14 5 10
    (by omega) hHcard.le (by decide)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
