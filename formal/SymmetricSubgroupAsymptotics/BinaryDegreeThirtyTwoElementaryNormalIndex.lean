import SymmetricSubgroupAsymptotics.BinarySplitElementary16PhiZeroOriginalRows
import SymmetricSubgroupAsymptotics.BinaryElementaryPhiZeroStabilizerBinding
import SymmetricSubgroupAsymptotics.BinaryPairCoordinateStabilizerKernelContainment
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoAbelianizationSaturation
import SymmetricSubgroupAsymptotics.BinaryDegreeEightLargeNormalIndex

/-! The elementary phi-zero critical state forces the SAME original
normal to contain the whole correlated pair kernel. Its own index is two;
its rank-nine lower bound then gives the full original abelianization1024. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open BinarySplitElementary16PhiZeroStabilizer
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))

theorem elementary_phi_zero_normal_contains_kernel_and_index_two
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hzero : F.top.range = E.splitAffineAction)
    (hH : E.top.range = BinaryEightOriginalRowActions.regularH)
    (hK : E.kernelSpace = (BinaryRegularEightNaturalRegistry.charts 23).2.space)
    (N : Subgroup U) [N.Normal]
    (hS : (E.originalCoordinateSubrepresentation
      (F.axisNaturalSubrepresentation (N ⊓ F.top.ker))).toSubmodule =
        (BinaryElementary16GraphHeadRigidity.stateChart 0).space)
    (hB : MarkedC4.normalGen (N ⊓ F.top.ker) = 6)
    (hindex : (N.map F.top.rangeRestrict).index = 2)
    (hcomm : ⁅F.top.ker,N⁆ ≤ primeRelativeRadical 2 (N ⊓ F.top.ker)) :
    F.top.ker ≤ N ∧ N.index = 2 := by
  let W := F.axisNaturalSubrepresentation (N ⊓ F.top.ker)
  have hcap : Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ 6 := by
    rw [← F.axisNatural_normalGen (N ⊓ F.top.ker) inf_le_right hU,hB]
  have hr := BinaryElementaryPhiZeroIntrinsicRadical.original_radical_eq E hzero hH hK W hS hcap
  have hR : (F.ambientAxis (primeRelativeRadical 2 (N ⊓ F.top.ker))).map
      E.originalCoordinateEquiv.toLinearMap = radical.space := by
    rw [F.axisNatural_radical (N ⊓ F.top.ker) inf_le_right]
    exact hr.trans BinaryElementaryPhiZeroStabilizerBinding.radical_eq_intrinsic.symm
  have hS' : (E.originalCoordinateSubrepresentation W).toSubmodule = state.space :=
    hS.trans BinaryElementaryPhiZeroStabilizerBinding.state_eq_original_graph.symm
  have hTopCard : Nat.card F.top.range = 16 := by
    rw [E.card_of_original_zero_frame hzero,hK,hH,
      (BinaryRegularEightNaturalRegistry.charts 23).2.card,BinaryMenuCayley8T3.exact_card]
    change 2 ^ 1 * 8 = 16
    norm_num
  have hDlarge : 2 < Nat.card (N.map F.top.rangeRestrict) := by
    have hc := (N.map F.top.rangeRestrict).card_mul_index
    rw [hindex,hTopCard] at hc
    omega
  have hker : F.top.ker ≤ N := by
    apply F.kernel_le_normal_of_coordinate_stabilizer E N state.space radical.space hS' hR hcomm
    intro K hfixed
    exact BinarySplitElementary16PhiZeroOriginalRows.kernel_le_original_zero_frame E hzero hH hK
      (N.map F.top.rangeRestrict) hDlarge K hfixed
  exact ⟨hker,(F.normal_index_eq_actual_image_index N hker).trans hindex⟩

theorem elementary_phi_zero_normal_abelianization_card
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hzero : F.top.range = E.splitAffineAction)
    (hH : E.top.range = BinaryEightOriginalRowActions.regularH)
    (hK : E.kernelSpace = (BinaryRegularEightNaturalRegistry.charts 23).2.space)
    (N : Subgroup U) [N.Normal]
    (hS : (E.originalCoordinateSubrepresentation
      (F.axisNaturalSubrepresentation (N ⊓ F.top.ker))).toSubmodule =
        (BinaryElementary16GraphHeadRigidity.stateChart 0).space)
    (hB : MarkedC4.normalGen (N ⊓ F.top.ker) = 6)
    (hindex : (N.map F.top.rangeRestrict).index = 2)
    (hcomm : ⁅F.top.ker,N⁆ ≤ primeRelativeRadical 2 (N ⊓ F.top.ker))
    (hN : 9 ≤ MarkedC4.normalGen N) : Nat.card (Abelianization U) = 1024 := by
  have hi := (F.elementary_phi_zero_normal_contains_kernel_and_index_two E hU hzero hH hK
    N hS hB hindex hcomm).2
  have hdegree : Nat.card X = 32 := by simpa only [Nat.card_fin] using F.card_points
  exact binary_degree_thirty_two_abelianization_card_of_index_two_normal_nine U hU hdegree N hi hN

end SymmetricSubgroupAsymptotics.BinaryPairFrame
