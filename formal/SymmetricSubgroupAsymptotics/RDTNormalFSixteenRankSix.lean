import SymmetricSubgroupAsymptotics.RDTNormalFRegularFortyFive
import SymmetricSubgroupAsymptotics.RDTNormalFRegularFortySix
import SymmetricSubgroupAsymptotics.RDTNormalFHeisenberg12
import SymmetricSubgroupAsymptotics.RDTNormalFHeisenberg13
import SymmetricSubgroupAsymptotics.RDTNormalFHeisenbergFour
import SymmetricSubgroupAsymptotics.CentralBinaryPairFrameExists
import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenHighRankTopModels

/-! The five retained kernel templates exhaust every rank-six binary
sixteen-point source. Every quotient keeps its SAME original normal.
There is no assumption about split lifts or a catalogue of original normals. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8)) [MulAction.IsPretransitive U X]
include F

theorem sixteen_rank_six_all_normal_quotients
    (hU : IsPGroup 2 U) (hrank : 6 ≤ MarkedC4.genRank U)
    (N : Subgroup U) [N.Normal]
    (hnonab : ¬ ∀ a b : U ⧸ N, a * b = b * a) :
    ∃ V : Subgroup (U ⧸ N), V.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog V +
        (5 / 4 : ℝ) * MarkedC4.ActualNormalFMarkedPeel.centralLog V ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog V ≤ 4 := by
  rcases F.six_le_genRank_literal_top_models hU hrank with
    ⟨g, hH, hhead⟩ | ⟨g, hH, hhead⟩
  · let F' := F.reindex g
    rcases F'.regular_large_axis_models hU F'.top.ker le_rfl hH (by dsimp only [F']; omega) with
      ⟨hK, hR⟩ | ⟨hK, hR⟩
    · rw [F'.ambientAxis_kernel] at hK
      exact F'.regular45_five_quarters_normalF_packet hU hrank hH hK hR N hnonab
    · rw [F'.ambientAxis_kernel] at hK
      exact F'.regular46_five_quarters_normalF_packet hU hrank hH hK N hnonab
  · let F' := F.reindex g
    rcases F'.heisenberg_large_axis_models hU F'.top.ker le_rfl hH (by dsimp only [F']; omega) with
      ⟨hK, hR⟩ | ⟨hK, hR⟩ | ⟨hK, hR⟩
    · rw [F'.ambientAxis_kernel] at hK
      exact F'.heisenberg12_five_quarters_normalF_packet hU hrank hH hK hR N hnonab
    · rw [F'.ambientAxis_kernel] at hK
      exact F'.heisenberg13_five_quarters_normalF_packet hU hrank hH hK hR N hnonab
    · rw [F'.ambientAxis_kernel] at hK
      exact F'.heisenbergFour_five_quarters_normalF_packet hU hrank hH hK hR N hnonab

end SymmetricSubgroupAsymptotics.BinaryPairFrame
