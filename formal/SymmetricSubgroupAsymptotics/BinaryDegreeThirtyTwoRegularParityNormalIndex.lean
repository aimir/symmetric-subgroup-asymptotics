import SymmetricSubgroupAsymptotics.BinaryRegularParityZeroOrbitOriginalRows
import SymmetricSubgroupAsymptotics.BinaryPairOriginalIndexTwoOrbitWitnessKernel
import SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroIntrinsicRadical
import SymmetricSubgroupAsymptotics.BinarySplitRegular46ParityZeroStabilizerCountData
import SymmetricSubgroupAsymptotics.BinaryPairCoordinateStabilizerKernelContainment
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoAbelianizationSaturation
import SymmetricSubgroupAsymptotics.BinaryDegreeEightLargeNormalIndex

/-! The regular parity-zero critical BinarySplitRegular46ParityZeroStabilizer.state forces the SAME original
normal to contain the whole correlated pair kernel. Its own index is two;
its rank-nine lower bound then gives the full original abelianization1024. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open BinarySplitRegular46ParityZeroStabilizer
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))

theorem regular_parity_zero_normal_contains_kernel_and_index_two
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hzero : F.top.range = E.splitAffineAction)
    (hH : E.top.range = BinaryEightOriginalRowActions.regularH)
    (hK : E.kernelSpace = (BinaryRegularEightNaturalRegistry.charts 46).2.space)
    (N : Subgroup U) [N.Normal]
    (hS : (E.originalCoordinateSubrepresentation
      (F.axisNaturalSubrepresentation (N ⊓ F.top.ker))).toSubmodule =
        (BinaryRegular46GraphHeadRigidity.stateChart 0).space)
    (hB : MarkedC4.normalGen (N ⊓ F.top.ker) = 4)
    (hindex : (N.map F.top.rangeRestrict).index = 2)
    (hcomm : ⁅F.top.ker,N⁆ ≤ primeRelativeRadical 2 (N ⊓ F.top.ker)) :
    F.top.ker ≤ N ∧ N.index = 2 := by
  let W : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 16)) :=
    F.axisNaturalSubrepresentation (N ⊓ F.top.ker)
  have hcap : Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ 4 := by
    rw [← F.axisNatural_normalGen (N ⊓ F.top.ker) inf_le_right hU,hB]
  have hr := BinaryRegular46ParityZeroIntrinsicRadical.original_radical_eq E hzero hH hK W hS hcap
  have hR : (F.ambientAxis (primeRelativeRadical 2 (N ⊓ F.top.ker))).map
      E.originalCoordinateEquiv.toLinearMap = BinarySplitRegular46ParityZeroStabilizer.radical.space := by
    rw [F.axisNatural_radical (N ⊓ F.top.ker) inf_le_right]
    exact hr
  have hdefect (v : Fin 16 → ZMod 2) :
      v-BinarySplitRegular46ParityZeroStabilizer.sectionMap (BinarySplitRegular46ParityZeroStabilizer.projection v) ∈ BinarySplitRegular46ParityZeroStabilizer.state.space :=
    linear_quotient_defect_mem_of_basis (k := ZMod 2) (w := 16) (d := 8)
      BinarySplitRegular46ParityZeroStabilizer.state.space BinarySplitRegular46ParityZeroStabilizer.projection BinarySplitRegular46ParityZeroStabilizer.sectionMap BinarySplitRegular46ParityZeroStabilizer.quotient_basis v
  have hwitness (c : Fin 8 → ZMod 2) (hc : c ≠ 0) :
      ∃ u : Fin 3 → F.top.range, ∀ i j : Fin 3, i ≠ j →
        E.originalCoordinateRepresentation (u i) (BinarySplitRegular46ParityZeroStabilizer.sectionMap c) -
          E.originalCoordinateRepresentation (u j) (BinarySplitRegular46ParityZeroStabilizer.sectionMap c) ∉ BinarySplitRegular46ParityZeroStabilizer.radical.space :=
    BinaryRegularParityZeroOrbitOriginalRows.exists_actual_three_orbit_witnesses
      E hzero hH hK c hc
  have hker : F.top.ker ≤ N := by
    apply F.kernel_le_normal_of_coordinate_stabilizer E N BinarySplitRegular46ParityZeroStabilizer.state.space BinarySplitRegular46ParityZeroStabilizer.radical.space hS hR hcomm
    intro K hfixed
    exact E.kernel_le_of_original_intrinsic_radical_three_orbit_witnesses
      (C := Fin 8 → ZMod 2) W BinarySplitRegular46ParityZeroStabilizer.state.space BinarySplitRegular46ParityZeroStabilizer.radical.space hS hr
      BinarySplitRegular46ParityZeroStabilizer.projection BinarySplitRegular46ParityZeroStabilizer.sectionMap hdefect hwitness (N.map F.top.rangeRestrict) hindex K hfixed
  exact ⟨hker,(F.normal_index_eq_actual_image_index N hker).trans hindex⟩

theorem regular_parity_zero_normal_abelianization_card
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hzero : F.top.range = E.splitAffineAction)
    (hH : E.top.range = BinaryEightOriginalRowActions.regularH)
    (hK : E.kernelSpace = (BinaryRegularEightNaturalRegistry.charts 46).2.space)
    (N : Subgroup U) [N.Normal]
    (hS : (E.originalCoordinateSubrepresentation
      (F.axisNaturalSubrepresentation (N ⊓ F.top.ker))).toSubmodule =
        (BinaryRegular46GraphHeadRigidity.stateChart 0).space)
    (hB : MarkedC4.normalGen (N ⊓ F.top.ker) = 4)
    (hindex : (N.map F.top.rangeRestrict).index = 2)
    (hcomm : ⁅F.top.ker,N⁆ ≤ primeRelativeRadical 2 (N ⊓ F.top.ker))
    (hN : 9 ≤ MarkedC4.normalGen N) : Nat.card (Abelianization U) = 1024 := by
  have hi := (F.regular_parity_zero_normal_contains_kernel_and_index_two E hU hzero hH hK
    N hS hB hindex hcomm).2
  have hdegree : Nat.card X = 32 := by simpa only [Nat.card_fin] using F.card_points
  exact binary_degree_thirty_two_abelianization_card_of_index_two_normal_nine U hU hdegree N hi hN

end SymmetricSubgroupAsymptotics.BinaryPairFrame
