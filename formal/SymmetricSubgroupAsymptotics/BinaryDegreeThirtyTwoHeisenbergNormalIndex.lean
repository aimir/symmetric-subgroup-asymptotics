import SymmetricSubgroupAsymptotics.BinaryHeisenbergPhiZeroOrbitOriginalRows
import SymmetricSubgroupAsymptotics.BinaryPairOriginalIndexTwoOrbitWitnessKernel
import SymmetricSubgroupAsymptotics.BinaryHeisenbergPhiZeroStabilizerBinding
import SymmetricSubgroupAsymptotics.BinaryPairCoordinateStabilizerKernelContainment
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoAbelianizationSaturation
import SymmetricSubgroupAsymptotics.BinaryDegreeEightLargeNormalIndex

/-! The Heisenberg phi-zero critical BinarySplitHeisenberg14PhiZeroStabilizer.state forces the SAME original
normal to contain the whole correlated pair kernel. Its own index is two;
its rank-nine lower bound then gives the full original abelianization1024. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open BinarySplitHeisenberg14PhiZeroStabilizer
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))

theorem heisenberg_phi_zero_normal_contains_kernel_and_index_two
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hzero : F.top.range = E.splitAffineAction)
    (hH : E.top.range = BinaryEightOriginalRowActions.heisenbergH)
    (hK : E.kernelSpace = (BinaryHeisenbergEightNaturalHeads.charts 14).2.space)
    (N : Subgroup U) [N.Normal]
    (hS : (E.originalCoordinateSubrepresentation
      (F.axisNaturalSubrepresentation (N ⊓ F.top.ker))).toSubmodule =
        (BinaryHeisenberg14GraphHeadRigidity.stateChart 0).space)
    (hB : MarkedC4.normalGen (N ⊓ F.top.ker) = 4)
    (hindex : (N.map F.top.rangeRestrict).index = 2)
    (hcomm : ⁅F.top.ker,N⁆ ≤ primeRelativeRadical 2 (N ⊓ F.top.ker)) :
    F.top.ker ≤ N ∧ N.index = 2 := by
  let W : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 16)) :=
    F.axisNaturalSubrepresentation (N ⊓ F.top.ker)
  have hcap : Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ 4 := by
    rw [← F.axisNatural_normalGen (N ⊓ F.top.ker) inf_le_right hU,hB]
  have hr := BinaryHeisenbergPhiZeroIntrinsicRadical.original_radical_eq E hzero hH hK W hS hcap
  have hrData : ((Representation.Coinvariants.ker W.toRepresentation).map
      W.toSubmodule.subtype).map E.originalCoordinateEquiv.toLinearMap = BinarySplitHeisenberg14PhiZeroStabilizer.radical.space :=
    hr.trans BinaryHeisenbergPhiZeroStabilizerBinding.radical_eq_intrinsic.symm
  have hR : (F.ambientAxis (primeRelativeRadical 2 (N ⊓ F.top.ker))).map
      E.originalCoordinateEquiv.toLinearMap = BinarySplitHeisenberg14PhiZeroStabilizer.radical.space := by
    rw [F.axisNatural_radical (N ⊓ F.top.ker) inf_le_right]
    exact hrData
  have hS' : (E.originalCoordinateSubrepresentation W).toSubmodule = BinarySplitHeisenberg14PhiZeroStabilizer.state.space :=
    hS.trans BinaryHeisenbergPhiZeroStabilizerBinding.state_eq_original_graph.symm
  have hdefect (v : Fin 16 → ZMod 2) :
      v-BinarySplitHeisenberg14PhiZeroStabilizer.sectionMap (BinarySplitHeisenberg14PhiZeroStabilizer.projection v) ∈ BinarySplitHeisenberg14PhiZeroStabilizer.state.space :=
    linear_quotient_defect_mem_of_basis (k := ZMod 2) (w := 16) (d := 6)
      BinarySplitHeisenberg14PhiZeroStabilizer.state.space BinarySplitHeisenberg14PhiZeroStabilizer.projection BinarySplitHeisenberg14PhiZeroStabilizer.sectionMap BinarySplitHeisenberg14PhiZeroStabilizer.quotient_basis v
  have hwitness (c : Fin 6 → ZMod 2) (hc : c ≠ 0) :
      ∃ u : Fin 3 → F.top.range, ∀ i j : Fin 3, i ≠ j →
        E.originalCoordinateRepresentation (u i) (BinarySplitHeisenberg14PhiZeroStabilizer.sectionMap c) -
          E.originalCoordinateRepresentation (u j) (BinarySplitHeisenberg14PhiZeroStabilizer.sectionMap c) ∉ BinarySplitHeisenberg14PhiZeroStabilizer.radical.space :=
    BinaryHeisenbergPhiZeroOrbitOriginalRows.exists_actual_three_orbit_witnesses
      E hzero hH hK c hc
  have hker : F.top.ker ≤ N := by
    apply F.kernel_le_normal_of_coordinate_stabilizer E N BinarySplitHeisenberg14PhiZeroStabilizer.state.space BinarySplitHeisenberg14PhiZeroStabilizer.radical.space hS' hR hcomm
    intro K hfixed
    exact E.kernel_le_of_original_intrinsic_radical_three_orbit_witnesses
      (C := Fin 6 → ZMod 2) W BinarySplitHeisenberg14PhiZeroStabilizer.state.space BinarySplitHeisenberg14PhiZeroStabilizer.radical.space hS' hrData
      BinarySplitHeisenberg14PhiZeroStabilizer.projection BinarySplitHeisenberg14PhiZeroStabilizer.sectionMap hdefect hwitness (N.map F.top.rangeRestrict) hindex K hfixed
  exact ⟨hker,(F.normal_index_eq_actual_image_index N hker).trans hindex⟩

theorem heisenberg_phi_zero_normal_abelianization_card
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hzero : F.top.range = E.splitAffineAction)
    (hH : E.top.range = BinaryEightOriginalRowActions.heisenbergH)
    (hK : E.kernelSpace = (BinaryHeisenbergEightNaturalHeads.charts 14).2.space)
    (N : Subgroup U) [N.Normal]
    (hS : (E.originalCoordinateSubrepresentation
      (F.axisNaturalSubrepresentation (N ⊓ F.top.ker))).toSubmodule =
        (BinaryHeisenberg14GraphHeadRigidity.stateChart 0).space)
    (hB : MarkedC4.normalGen (N ⊓ F.top.ker) = 4)
    (hindex : (N.map F.top.rangeRestrict).index = 2)
    (hcomm : ⁅F.top.ker,N⁆ ≤ primeRelativeRadical 2 (N ⊓ F.top.ker))
    (hN : 9 ≤ MarkedC4.normalGen N) : Nat.card (Abelianization U) = 1024 := by
  have hi := (F.heisenberg_phi_zero_normal_contains_kernel_and_index_two E hU hzero hH hK
    N hS hB hindex hcomm).2
  have hdegree : Nat.card X = 32 := by simpa only [Nat.card_fin] using F.card_points
  exact binary_degree_thirty_two_abelianization_card_of_index_two_normal_nine U hU hdegree N hi hN

end SymmetricSubgroupAsymptotics.BinaryPairFrame
