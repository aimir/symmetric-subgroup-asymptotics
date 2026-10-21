import SymmetricSubgroupAsymptotics.BinaryPairAxisNaturalModule
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoNonelementarySaturation
import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenJointZeroFrames
import SymmetricSubgroupAsymptotics.BinaryPairWideOriginalLayers
import SymmetricSubgroupAsymptotics.BinaryPairOriginalGraphRigidity
import SymmetricSubgroupAsymptotics.BinaryPairFullConstantOriginalState

/-! A hypothetical proper rank-nine normal in an original rank-at-most-nine
source selects three literal inner zero-frame states. The submodule is
the actual intersection N∩ker throughout; no independent normal subgroup
or action-classification assumption enters the conclusion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16))

theorem nonelementary_rank_nine_normal_actual_zero_templates
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hgen : MarkedC4.genRank U ≤ 9)
    (hnon : ¬BinarySquareActionStructure.SquaresActTrivially (G := F.top.range) (X := Fin 16))
    (N : Subgroup U) [N.Normal] (hproper : N ≠ ⊤) (hN : 9 ≤ MarkedC4.normalGen N) :
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
  obtain ⟨_,hB,_,hTopRank,_,_,_⟩ :=
    F.nonelementary_proper_normal_nine_saturation hU hgen hnon N hproper hN
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

end SymmetricSubgroupAsymptotics.BinaryPairFrame
