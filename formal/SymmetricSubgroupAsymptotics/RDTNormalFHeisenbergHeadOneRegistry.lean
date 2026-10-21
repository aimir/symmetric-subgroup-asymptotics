import SymmetricSubgroupAsymptotics.RDTNormalFHeisenbergLowHeadUnit
import SymmetricSubgroupAsymptotics.BinaryHeisenberg2AllJointAxes
import SymmetricSubgroupAsymptotics.BinaryHeisenberg3AllJointAxes
import SymmetricSubgroupAsymptotics.BinaryHeisenberg4AllJointAxes
import SymmetricSubgroupAsymptotics.BinaryHeisenberg5AllJointAxes
import SymmetricSubgroupAsymptotics.BinaryHeisenberg6AllJointAxes
import SymmetricSubgroupAsymptotics.BinaryHeisenberg7AllJointAxes
import SymmetricSubgroupAsymptotics.BinaryHeisenberg8AllJointAxes
import SymmetricSubgroupAsymptotics.BinaryHeisenberg9AllJointAxes
import SymmetricSubgroupAsymptotics.BinaryHeisenberg10AllJointAxes
import SymmetricSubgroupAsymptotics.BinaryHeisenberg11AllJointAxes

/-! The same unit installer covers all ten head-one states of the checked
Heisenberg registry. This assembles their fixed linear certificates; it
does not enumerate original extensions or normal subgroups. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open BinaryHeisenbergEightNaturalHeads
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8))

theorem heisenberg_head_one_registry_unit_normalF_packet
    (hU : IsPGroup 2 U) (hrank : 5 ≤ MarkedC4.genRank U) (hH : F.top.range = H)
    (i : Fin 15) (hi : 2 ≤ i.val ∧ i.val < 12)
    (hK : F.kernelSpace = (charts i).2.space)
    (hR : F.ambientAxis (primeRelativeRadical 2 F.top.ker) = (radicalCharts i).2.space)
    (N : Subgroup U) [N.Normal]
    (hnonab : ¬ ∀ a b : U ⧸ N, a*b=b*a) :
    ∃ W : Subgroup (U ⧸ N), W.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog W +
        MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 4 := by
  fin_cases i
  · norm_num at hi
  · norm_num at hi
  · change F.kernelSpace = BinaryRegularEightNaturalRegistry.chart24.space at hK
    change F.ambientAxis (primeRelativeRadical 2 F.top.ker) = BinaryRegularEightNaturalRegistry.chart33.space at hR
    apply F.heisenberg_low_head_unit_normalF_packet hU hrank hH
      BinaryRegularEightNaturalRegistry.chart24.space BinaryRegularEightNaturalRegistry.chart33.space hK hR
      (BinaryRegularEightNaturalRegistry.chart33.le_of_basis_mem _ (by decide +kernel))
      (by rw [BinaryRegularEightNaturalRegistry.chart24.card,BinaryRegularEightNaturalRegistry.chart33.card]; decide) _ N hnonab
    intro A hA
    simpa only [BinaryRegularEightNaturalRegistry.chart33.card] using BinaryHeisenberg2AllJointAxes.all_axes A hA
  · change F.kernelSpace = BinaryRegularEightNaturalRegistry.chart4.space at hK
    change F.ambientAxis (primeRelativeRadical 2 F.top.ker) = BinaryRegularEightNaturalRegistry.chart40.space at hR
    apply F.heisenberg_low_head_unit_normalF_packet hU hrank hH
      BinaryRegularEightNaturalRegistry.chart4.space BinaryRegularEightNaturalRegistry.chart40.space hK hR
      (BinaryRegularEightNaturalRegistry.chart40.le_of_basis_mem _ (by decide +kernel))
      (by rw [BinaryRegularEightNaturalRegistry.chart4.card,BinaryRegularEightNaturalRegistry.chart40.card]; decide) _ N hnonab
    intro A hA
    simpa only [BinaryRegularEightNaturalRegistry.chart40.card] using BinaryHeisenberg3AllJointAxes.all_axes A hA
  · change F.kernelSpace = BinaryRegularEightNaturalRegistry.chart31.space at hK
    change F.ambientAxis (primeRelativeRadical 2 F.top.ker) = BinaryRegularEightNaturalRegistry.chart33.space at hR
    apply F.heisenberg_low_head_unit_normalF_packet hU hrank hH
      BinaryRegularEightNaturalRegistry.chart31.space BinaryRegularEightNaturalRegistry.chart33.space hK hR
      (BinaryRegularEightNaturalRegistry.chart33.le_of_basis_mem _ (by decide +kernel))
      (by rw [BinaryRegularEightNaturalRegistry.chart31.card,BinaryRegularEightNaturalRegistry.chart33.card]; decide) _ N hnonab
    intro A hA
    simpa only [BinaryRegularEightNaturalRegistry.chart33.card] using BinaryHeisenberg4AllJointAxes.all_axes A hA
  · change F.kernelSpace = BinaryRegularEightNaturalRegistry.chart32.space at hK
    change F.ambientAxis (primeRelativeRadical 2 F.top.ker) = BinaryRegularEightNaturalRegistry.chart33.space at hR
    apply F.heisenberg_low_head_unit_normalF_packet hU hrank hH
      BinaryRegularEightNaturalRegistry.chart32.space BinaryRegularEightNaturalRegistry.chart33.space hK hR
      (BinaryRegularEightNaturalRegistry.chart33.le_of_basis_mem _ (by decide +kernel))
      (by rw [BinaryRegularEightNaturalRegistry.chart32.card,BinaryRegularEightNaturalRegistry.chart33.card]; decide) _ N hnonab
    intro A hA
    simpa only [BinaryRegularEightNaturalRegistry.chart33.card] using BinaryHeisenberg5AllJointAxes.all_axes A hA
  · change F.kernelSpace = BinaryRegularEightNaturalRegistry.chart13.space at hK
    change F.ambientAxis (primeRelativeRadical 2 F.top.ker) = BinaryRegularEightNaturalRegistry.chart23.space at hR
    apply F.heisenberg_low_head_unit_normalF_packet hU hrank hH
      BinaryRegularEightNaturalRegistry.chart13.space BinaryRegularEightNaturalRegistry.chart23.space hK hR
      (BinaryRegularEightNaturalRegistry.chart23.le_of_basis_mem _ (by decide +kernel))
      (by rw [BinaryRegularEightNaturalRegistry.chart13.card,BinaryRegularEightNaturalRegistry.chart23.card]; decide) _ N hnonab
    intro A hA
    simpa only [BinaryRegularEightNaturalRegistry.chart23.card] using BinaryHeisenberg6AllJointAxes.all_axes A hA
  · change F.kernelSpace = BinaryRegularEightNaturalRegistry.chart15.space at hK
    change F.ambientAxis (primeRelativeRadical 2 F.top.ker) = BinaryRegularEightNaturalRegistry.chart40.space at hR
    apply F.heisenberg_low_head_unit_normalF_packet hU hrank hH
      BinaryRegularEightNaturalRegistry.chart15.space BinaryRegularEightNaturalRegistry.chart40.space hK hR
      (BinaryRegularEightNaturalRegistry.chart40.le_of_basis_mem _ (by decide +kernel))
      (by rw [BinaryRegularEightNaturalRegistry.chart15.card,BinaryRegularEightNaturalRegistry.chart40.card]; decide) _ N hnonab
    intro A hA
    simpa only [BinaryRegularEightNaturalRegistry.chart40.card] using BinaryHeisenberg7AllJointAxes.all_axes A hA
  · change F.kernelSpace = BinaryRegularEightNaturalRegistry.chart46.space at hK
    change F.ambientAxis (primeRelativeRadical 2 F.top.ker) = BinaryRegularEightNaturalRegistry.chart40.space at hR
    apply F.heisenberg_low_head_unit_normalF_packet hU hrank hH
      BinaryRegularEightNaturalRegistry.chart46.space BinaryRegularEightNaturalRegistry.chart40.space hK hR
      (BinaryRegularEightNaturalRegistry.chart40.le_of_basis_mem _ (by decide +kernel))
      (by rw [BinaryRegularEightNaturalRegistry.chart46.card,BinaryRegularEightNaturalRegistry.chart40.card]; decide) _ N hnonab
    intro A hA
    simpa only [BinaryRegularEightNaturalRegistry.chart40.card] using BinaryHeisenberg8AllJointAxes.all_axes A hA
  · change F.kernelSpace = BinaryRegularEightNaturalRegistry.chart21.space at hK
    change F.ambientAxis (primeRelativeRadical 2 F.top.ker) = BinaryRegularEightNaturalRegistry.chart23.space at hR
    apply F.heisenberg_low_head_unit_normalF_packet hU hrank hH
      BinaryRegularEightNaturalRegistry.chart21.space BinaryRegularEightNaturalRegistry.chart23.space hK hR
      (BinaryRegularEightNaturalRegistry.chart23.le_of_basis_mem _ (by decide +kernel))
      (by rw [BinaryRegularEightNaturalRegistry.chart21.card,BinaryRegularEightNaturalRegistry.chart23.card]; decide) _ N hnonab
    intro A hA
    simpa only [BinaryRegularEightNaturalRegistry.chart23.card] using BinaryHeisenberg9AllJointAxes.all_axes A hA
  · change F.kernelSpace = BinaryRegularEightNaturalRegistry.chart22.space at hK
    change F.ambientAxis (primeRelativeRadical 2 F.top.ker) = BinaryRegularEightNaturalRegistry.chart23.space at hR
    apply F.heisenberg_low_head_unit_normalF_packet hU hrank hH
      BinaryRegularEightNaturalRegistry.chart22.space BinaryRegularEightNaturalRegistry.chart23.space hK hR
      (BinaryRegularEightNaturalRegistry.chart23.le_of_basis_mem _ (by decide +kernel))
      (by rw [BinaryRegularEightNaturalRegistry.chart22.card,BinaryRegularEightNaturalRegistry.chart23.card]; decide) _ N hnonab
    intro A hA
    simpa only [BinaryRegularEightNaturalRegistry.chart23.card] using BinaryHeisenberg10AllJointAxes.all_axes A hA
  · change F.kernelSpace = BinaryRegularEightNaturalRegistry.chart23.space at hK
    change F.ambientAxis (primeRelativeRadical 2 F.top.ker) = BinaryRegularEightNaturalRegistry.chart0.space at hR
    apply F.heisenberg_low_head_unit_normalF_packet hU hrank hH
      BinaryRegularEightNaturalRegistry.chart23.space BinaryRegularEightNaturalRegistry.chart0.space hK hR
      (BinaryRegularEightNaturalRegistry.chart0.le_of_basis_mem _ (by decide +kernel))
      (by rw [BinaryRegularEightNaturalRegistry.chart23.card,BinaryRegularEightNaturalRegistry.chart0.card]; decide) _ N hnonab
    intro A hA
    simpa only [BinaryRegularEightNaturalRegistry.chart0.card] using BinaryHeisenberg11AllJointAxes.all_axes A hA
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi

end SymmetricSubgroupAsymptotics.BinaryPairFrame
