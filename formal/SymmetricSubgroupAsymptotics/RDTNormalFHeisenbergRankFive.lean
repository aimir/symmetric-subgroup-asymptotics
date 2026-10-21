import SymmetricSubgroupAsymptotics.BinaryPairHeisenbergAllKernelModels
import SymmetricSubgroupAsymptotics.RDTNormalFHeisenbergHeadOneRegistry
import SymmetricSubgroupAsymptotics.RDTNormalFHeisenbergFullKernelUnit
import SymmetricSubgroupAsymptotics.RDTNormalFHeisenberg12Unit
import SymmetricSubgroupAsymptotics.RDTNormalFHeisenberg13Unit
import SymmetricSubgroupAsymptotics.RDTNormalFHeisenberg14Unit
import SymmetricSubgroupAsymptotics.RDTNormalFSmallSixteenOrder
import SymmetricSubgroupAsymptotics.NormalFPacketCoefficientMono

/-! All original Heisenberg-top rank-five pair actions and all their
nonabelian normal quotients, including arbitrary affine lifts. The complete
fifteen-state natural registry is assembled by two reusable installers. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open BinaryHeisenbergEightNaturalHeads
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8))

theorem heisenberg_rank_five_all_normal_quotients_unit
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hrank : 5 ≤ MarkedC4.genRank U) (hH : F.top.range = H)
    (N : Subgroup U) [N.Normal]
    (hnonab : ¬ ∀ a b : U ⧸ N, a*b=b*a) :
    ∃ W : Subgroup (U ⧸ N), W.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog W +
        MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 4 := by
  obtain ⟨i,hK,hR⟩ := F.heisenberg_all_kernel_models hH
  fin_cases i
  · have hu := (F.heisenberg_rank_five_derived_le_kernel_card hU hrank hH).1
    rw [hK] at hu
    change Nat.card U = 32 * Nat.card (charts 0).2.space at hu
    rw [(charts 0).2.card] at hu
    have hzero : (charts 0).1 = 0 := rfl
    rw [hzero] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · exact F.heisenberg_full_kernel_unit_normalF_packet hU hrank hH hK hR N hnonab
  · exact F.heisenberg_head_one_registry_unit_normalF_packet hU hrank hH 2
      (by decide) hK hR N hnonab
  · exact F.heisenberg_head_one_registry_unit_normalF_packet hU hrank hH 3
      (by decide) hK hR N hnonab
  · exact F.heisenberg_head_one_registry_unit_normalF_packet hU hrank hH 4
      (by decide) hK hR N hnonab
  · exact F.heisenberg_head_one_registry_unit_normalF_packet hU hrank hH 5
      (by decide) hK hR N hnonab
  · exact F.heisenberg_head_one_registry_unit_normalF_packet hU hrank hH 6
      (by decide) hK hR N hnonab
  · exact F.heisenberg_head_one_registry_unit_normalF_packet hU hrank hH 7
      (by decide) hK hR N hnonab
  · exact F.heisenberg_head_one_registry_unit_normalF_packet hU hrank hH 8
      (by decide) hK hR N hnonab
  · exact F.heisenberg_head_one_registry_unit_normalF_packet hU hrank hH 9
      (by decide) hK hR N hnonab
  · exact F.heisenberg_head_one_registry_unit_normalF_packet hU hrank hH 10
      (by decide) hK hR N hnonab
  · exact F.heisenberg_head_one_registry_unit_normalF_packet hU hrank hH 11
      (by decide) hK hR N hnonab
  · exact F.heisenberg12_unit_normalF_packet hU hrank hH
      (hK.trans kernel12_space) (hR.trans radical12_space) N hnonab
  · exact F.heisenberg13_unit_normalF_packet hU hrank hH
      (hK.trans kernel13_space) (hR.trans radical13_space) N hnonab
  · exact F.heisenberg14_unit_normalF_packet hU hrank hH
      (hK.trans kernel14_space) (hR.trans radical14_space) N hnonab

end SymmetricSubgroupAsymptotics.BinaryPairFrame
