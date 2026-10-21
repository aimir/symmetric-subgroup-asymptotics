import SymmetricSubgroupAsymptotics.BinarySplitRegular46FullConstantOriginalRadical
import SymmetricSubgroupAsymptotics.BinaryPairCoordinateStabilizerKernelContainment
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoAbelianizationSaturation
import SymmetricSubgroupAsymptotics.BinaryDegreeEightLargeNormalIndex

/-! The full-constant critical state forces the same original normal to
contain the full correlated pair kernel. Its own index is then two and
its rank-nine lower bound saturates the original abelianization order. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open BinarySplitRegular46FullConstantStabilizer
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))

theorem fullconstant_normal_contains_kernel_and_index_two
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hzero : F.top.range = E.splitAffineAction)
    (hH : E.top.range = BinaryEightOriginalRowActions.regularH)
    (hK : E.kernelSpace = (BinaryRegularEightNaturalRegistry.charts 46).2.space)
    (N : Subgroup U) [N.Normal]
    (hS : (E.originalCoordinateSubrepresentation
      (F.axisNaturalSubrepresentation (N ⊓ F.top.ker))).toSubmodule = state.space)
    (hB : MarkedC4.normalGen (N ⊓ F.top.ker) = 4)
    (hindex : (N.map F.top.rangeRestrict).index = 2)
    (hcomm : ⁅F.top.ker, N⁆ ≤ primeRelativeRadical 2 (N ⊓ F.top.ker)) :
    F.top.ker ≤ N ∧ N.index = 2 := by
  let W := F.axisNaturalSubrepresentation (N ⊓ F.top.ker)
  have hcap : Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ 4 := by
    rw [← F.axisNatural_normalGen (N ⊓ F.top.ker) inf_le_right hU, hB]
  have hr := BinarySplitRegular46FullConstantOriginalRadical.original_radical_eq E hzero hH hK W hS hcap
  have hR : (F.ambientAxis (primeRelativeRadical 2 (N ⊓ F.top.ker))).map
      E.originalCoordinateEquiv.toLinearMap = radical.space := by
    rw [F.axisNatural_radical (N ⊓ F.top.ker) inf_le_right]
    exact hr
  have hTopCard : Nat.card F.top.range = 128 := by
    rw [E.card_of_original_zero_frame hzero, hK, hH,
      (BinaryRegularEightNaturalRegistry.charts 46).2.card, BinaryMenuCayley8T3.exact_card]
    change 2 ^ 4 * 8 = 128
    norm_num
  have hDlarge : 16 < Nat.card (N.map F.top.rangeRestrict) := by
    have hc := (N.map F.top.rangeRestrict).card_mul_index
    rw [hindex, hTopCard] at hc
    omega
  have hker : F.top.ker ≤ N := by
    apply F.kernel_le_normal_of_coordinate_stabilizer E N state.space radical.space hS hR hcomm
    intro K hfixed
    exact BinarySplitRegular46FullConstantOriginalRows.kernel_le_original_zero_frame E hzero hH hK
      (N.map F.top.rangeRestrict) hDlarge K hfixed
  exact ⟨hker, (F.normal_index_eq_actual_image_index N hker).trans hindex⟩

theorem fullconstant_normal_abelianization_card
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hzero : F.top.range = E.splitAffineAction)
    (hH : E.top.range = BinaryEightOriginalRowActions.regularH)
    (hK : E.kernelSpace = (BinaryRegularEightNaturalRegistry.charts 46).2.space)
    (N : Subgroup U) [N.Normal]
    (hS : (E.originalCoordinateSubrepresentation
      (F.axisNaturalSubrepresentation (N ⊓ F.top.ker))).toSubmodule = state.space)
    (hB : MarkedC4.normalGen (N ⊓ F.top.ker) = 4)
    (hindex : (N.map F.top.rangeRestrict).index = 2)
    (hcomm : ⁅F.top.ker, N⁆ ≤ primeRelativeRadical 2 (N ⊓ F.top.ker))
    (hN : 9 ≤ MarkedC4.normalGen N) : Nat.card (Abelianization U) = 1024 := by
  have hi := (F.fullconstant_normal_contains_kernel_and_index_two E hU hzero hH hK N hS hB hindex hcomm).2
  have hdegree : Nat.card X = 32 := by simpa only [Nat.card_fin] using F.card_points
  exact binary_degree_thirty_two_abelianization_card_of_index_two_normal_nine U hU hdegree N hi hN

end SymmetricSubgroupAsymptotics.BinaryPairFrame
