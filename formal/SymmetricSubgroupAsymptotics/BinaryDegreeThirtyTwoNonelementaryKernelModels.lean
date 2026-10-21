import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoRankTenUniformSix
import SymmetricSubgroupAsymptotics.BinaryPairFullConstantOriginalState

/-! Original rank-ten sources with nonelementary top select the same
three original kernel states used by the sharp excess proof. No normal
denominator, outer splitting, or finite group catalogue is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance nonelementaryKernelModelsFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16))
include F

theorem rank_ten_nonelementary_original_kernel_models
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hhigh : 10≤MarkedC4.genRank U)
    (hnon : ¬ ∀ t : F.top.range,t^2=1) :
    MarkedC4.genRank U=10 ∧ MarkedC4.normalGen F.top.ker=4 ∧
      MarkedC4.genRank F.top.range=6 ∧
      ∃ E : BinaryPairFrame F.top.range (Fin 8), F.top.range=E.splitAffineAction ∧
        ((E.top.range=BinaryRegularEightNaturalRegistry.H ∧
          E.kernelSpace=(BinaryRegularEightNaturalRegistry.charts 46).2.space ∧
          ((E.originalCoordinateSubrepresentation (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule=
              (BinaryRegular46GraphHeadRigidity.stateChart 0).space ∨
           (E.originalCoordinateSubrepresentation (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule=
              BinarySplitRegular46FullConstantStabilizer.state.space)) ∨
         (E.top.range=BinaryHeisenbergEightNaturalHeads.H ∧
          E.kernelSpace=(BinaryHeisenbergEightNaturalHeads.charts 14).2.space ∧
          (E.originalCoordinateSubrepresentation (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule=
            (BinaryHeisenberg14GraphHeadRigidity.stateChart 0).space)) := by
  letI : MulAction.IsPretransitive F.top.range (Fin 16) := F.top_pretransitive
  have hTop := F.top_isPGroup hU
  letI : Group.IsNilpotent F.top.range := hTop.isNilpotent
  let W := F.axisNaturalSubrepresentation F.top.ker
  have hker : MarkedC4.normalGen F.top.ker=
      Module.finrank (ZMod 2) W.toRepresentation.Coinvariants :=
    F.axisNatural_normalGen F.top.ker le_rfl hU
  have hc := twoGroup_faithful_permutationSubrepresentationHead_le_quarter hTop hnon W
  rw [representationHead_finrank_eq_coinvariants] at hc
  norm_num only [Nat.card_fin] at hc
  have ht := twoGroup_transitive_normalGen_le_quarter_add_two F.top.range hTop (⊤ : Subgroup F.top.range)
  norm_num only [Nat.card_fin] at ht
  have htop := (MarkedC4.genRank_le_normalGen_top (G := F.top.range)).trans ht
  letI : IsMulCommutative F.top.ker := ⟨⟨fun a b => F.bitsHom_injective (by
    rw [map_mul,map_mul,mul_comm])⟩⟩
  letI : IsMulCommutative F.top.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    infer_instance
  have hg := AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen
    F.top.rangeRestrict F.top.rangeRestrict_surjective
  rw [MonoidHom.ker_rangeRestrict] at hg
  have htopHigh : 6≤MarkedC4.genRank F.top.range := by omega
  have hwide : 4≤Module.finrank (ZMod 2) W.toRepresentation.Coinvariants := by omega
  refine ⟨by omega,by omega,by omega,?_⟩
  obtain ⟨E₀⟩ := transitiveBinaryPairFrame_nonempty 3 F.top.range hTop (by norm_num only [Nat.card_fin])
  obtain ⟨E,hzero,hmodels⟩ := E₀.exists_joint_zero_frame hTop htopHigh W hwide
  refine ⟨E,hzero,?_⟩
  rcases hmodels with ⟨hH,hK,_⟩ | ⟨hH,hK,_⟩
  · have hchart : E.kernelSpace=(BinaryRegularEightNaturalRegistry.charts 46).2.space := by
      rw [←BinaryRegularEightNaturalRegistry.states_space,
        BinaryRegularEightNaturalRegistry.kernel46_space]
      exact hK
    rcases E.regular46_four_le_head_forces_original_layers hH hchart W hwide with
      ⟨hS,hL⟩ | ⟨hS,hL⟩
    · exact Or.inl ⟨hH,hchart,Or.inl (E.regular_parity_original_zero_graph hzero hH hK W hS hL hwide)⟩
    · exact Or.inl ⟨hH,hchart,Or.inr (E.regular_fullconstant_layers_original_state W hS hL)⟩
  · have hchart : E.kernelSpace=(BinaryHeisenbergEightNaturalHeads.charts 14).2.space := by
      rw [←BinaryHeisenbergEightNaturalHeads.states_space,
        BinaryHeisenbergEightNaturalHeads.kernel14_space]
      exact hK
    obtain ⟨hS,hL⟩ := E.heisenberg14_four_le_head_forces_original_layers hH hchart W hwide
    exact Or.inr ⟨hH,hchart,E.heisenberg_parity_original_zero_graph hzero hH hK W hS hL hwide⟩

end SymmetricSubgroupAsymptotics.BinaryPairFrame
