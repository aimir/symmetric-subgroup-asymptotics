import SymmetricSubgroupAsymptotics.BinaryPairAxisNaturalModule
import SymmetricSubgroupAsymptotics.NormalIntegralCoinvariantSaturation
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoRegularParityNormalIndex
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoFullConstantNormalIndex
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoHeisenbergNormalIndex
import SymmetricSubgroupAsymptotics.BinaryPairCentralKernel
import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenJointZeroFrames
import SymmetricSubgroupAsymptotics.BinaryPairWideOriginalLayers
import SymmetricSubgroupAsymptotics.BinaryPairOriginalGraphRigidity
import SymmetricSubgroupAsymptotics.BinaryPairFullConstantOriginalState

/-! The original four-head axis templates require only the actual top
rank and axis head, not a normal-rank hypothesis. Integral saturation
therefore reuses the checked mixed-radical index-two argument. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance rankSixIntegralAxisFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16))

theorem rank_six_four_axis_actual_zero_templates
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hTopRank : 6≤MarkedC4.genRank F.top.range)
    (N : Subgroup U) [N.Normal] (hB : MarkedC4.normalGen (N⊓F.top.ker)=4) :
    ∃ E : BinaryPairFrame F.top.range (Fin 8), F.top.range = E.splitAffineAction ∧
      ((E.top.range = BinaryRegularEightNaturalRegistry.H ∧
        E.kernelSpace = (BinaryRegularEightNaturalRegistry.charts 46).2.space ∧
        ((E.originalCoordinateSubrepresentation
          (F.axisNaturalSubrepresentation (N ⊓ F.top.ker))).toSubmodule =
            (BinaryRegular46GraphHeadRigidity.stateChart 0).space ∨
         (E.originalCoordinateSubrepresentation
          (F.axisNaturalSubrepresentation (N ⊓ F.top.ker))).toSubmodule =
            BinarySplitRegular46FullConstantStabilizer.state.space)) ∨
       (E.top.range = BinaryHeisenbergEightNaturalHeads.H ∧
        E.kernelSpace = (BinaryHeisenbergEightNaturalHeads.charts 14).2.space ∧
        (E.originalCoordinateSubrepresentation
          (F.axisNaturalSubrepresentation (N ⊓ F.top.ker))).toSubmodule =
            (BinaryHeisenberg14GraphHeadRigidity.stateChart 0).space)) := by
  letI : MulAction.IsPretransitive F.top.range (Fin 16) := F.top_pretransitive
  have hTop := F.top_isPGroup hU
  let W := F.axisNaturalSubrepresentation (N ⊓ F.top.ker)
  have hwide : 4 ≤ Module.finrank (ZMod 2) W.toRepresentation.Coinvariants := by
    rw [← F.axisNatural_normalGen (N ⊓ F.top.ker) inf_le_right hU,hB]
  obtain ⟨E₀⟩ := transitiveBinaryPairFrame_nonempty 3 F.top.range hTop
    (by norm_num only [Nat.card_fin])
  obtain ⟨E,hzero,hmodels⟩ := E₀.exists_joint_zero_frame hTop hTopRank W hwide
  refine ⟨E,hzero,?_⟩
  rcases hmodels with ⟨hH,hK,_⟩ | ⟨hH,hK,_⟩
  · have hchart : E.kernelSpace = (BinaryRegularEightNaturalRegistry.charts 46).2.space := by
      rw [← BinaryRegularEightNaturalRegistry.kernel46_space,
        BinaryRegularEightNaturalRegistry.states_space] at hK
      exact hK
    rcases E.regular46_four_le_head_forces_original_layers hH hchart W hwide with
      ⟨hS,hL⟩ | ⟨hS,hL⟩
    · exact Or.inl ⟨hH,hchart,Or.inl (E.regular_parity_original_zero_graph
        hzero hH (by
          rw [← BinaryRegularEightNaturalRegistry.kernel46_space,
            BinaryRegularEightNaturalRegistry.states_space]
          exact hchart) W hS hL hwide)⟩
    · exact Or.inl ⟨hH,hchart,Or.inr (E.regular_fullconstant_layers_original_state W hS hL)⟩
  · have hchart : E.kernelSpace = (BinaryHeisenbergEightNaturalHeads.charts 14).2.space := by
      rw [← BinaryHeisenbergEightNaturalHeads.kernel14_space,
        BinaryHeisenbergEightNaturalHeads.states_space] at hK
      exact hK
    obtain ⟨hS,hL⟩ := E.heisenberg14_four_le_head_forces_original_layers hH hchart W hwide
    exact Or.inr ⟨hH,hchart,E.heisenberg_parity_original_zero_graph
      hzero hH (by
        rw [← BinaryHeisenbergEightNaturalHeads.kernel14_space,
          BinaryHeisenbergEightNaturalHeads.states_space]
        exact hchart) W hS hL hwide⟩

/-- Full integral equality has the same actual mixed-radical conclusion
as ordinary-head equality; the checked orbit witnesses force index two. -/
theorem rank_six_four_axis_integral_saturation_index_two
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hTopRank : 6≤MarkedC4.genRank F.top.range)
    (N : Subgroup U) [N.Normal] (hB : MarkedC4.normalGen (N⊓F.top.ker)=4)
    (hindex : (N.map F.top.rangeRestrict).index=2)
    (hsat : normalIntegralCoinvariantOrder N=
      2^MarkedC4.normalGen (N⊓F.top.ker)*normalIntegralCoinvariantOrder (N.map F.top.rangeRestrict)) :
    N.index=2 := by
  have hpow (k : F.top.rangeRestrict.ker) : (k : U)^2=1 := by
    have hk : F.top (k : U)=1 := congrArg Subtype.val k.property
    exact F.kernel_square ⟨k.val,hk⟩
  have hsat' : normalIntegralCoinvariantOrder N=
      2^MarkedC4.normalGen (N⊓F.top.rangeRestrict.ker)*
        normalIntegralCoinvariantOrder (N.map F.top.rangeRestrict) := by
    simpa only [MonoidHom.ker_rangeRestrict] using hsat
  have hcomm : ⁅F.top.ker,N⁆≤primeRelativeRadical 2 (N⊓F.top.ker) := by
    simpa only [MonoidHom.ker_rangeRestrict] using
      kernel_mixed_commutator_le_radical_of_integral_saturation 2 hU
        F.top.rangeRestrict F.top.rangeRestrict_surjective hpow N hsat'
  obtain ⟨E,hzero,hmodels⟩ := F.rank_six_four_axis_actual_zero_templates hU hTopRank N hB
  rcases hmodels with ⟨hH,hK,hS|hS⟩ | ⟨hH,hK,hS⟩
  · exact (F.regular_parity_zero_normal_contains_kernel_and_index_two E hU hzero hH hK
      N hS hB hindex hcomm).2
  · exact (F.fullconstant_normal_contains_kernel_and_index_two E hU hzero hH hK
      N hS hB hindex hcomm).2
  · exact (F.heisenberg_phi_zero_normal_contains_kernel_and_index_two E hU hzero hH hK
      N hS hB hindex hcomm).2

end SymmetricSubgroupAsymptotics.BinaryPairFrame
