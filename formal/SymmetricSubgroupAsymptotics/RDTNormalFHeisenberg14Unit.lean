import SymmetricSubgroupAsymptotics.RDTNormalFHeisenbergUnitAxisEnvelope
import SymmetricSubgroupAsymptotics.BinaryHeisenbergRankFiveCards
import SymmetricSubgroupAsymptotics.BinaryHeisenberg14AllJointAxes

/-! The retained K14 joint envelope also covers every original rank-five
extension at unit coefficient, including all nonabelian normal quotients.
No rank-six saturation or zero affine lift is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8))
open BinaryRegularEightNaturalRegistry (chart40 chart23)

theorem heisenberg14_unit_normalF_packet
    (hU : IsPGroup 2 U) (hrank : 5 ≤ MarkedC4.genRank U)
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (hK : F.kernelSpace = BinaryHeisenbergEightSquareCarry.K14)
    (hR : F.ambientAxis (primeRelativeRadical 2 F.top.ker) = BinaryHeisenbergEightSquareCarry.R14)
    (N : Subgroup U) [N.Normal]
    (hnonab : ¬ ∀ a b : U ⧸ N, a * b = b * a) :
    ∃ W : Subgroup (U ⧸ N), W.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog W +
        MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 4 := by
  have hKC : F.kernelSpace = chart40.space :=
    hK.trans BinaryHeisenbergEightNaturalHeads.kernel14_space.symm
  have hRC : F.ambientAxis (primeRelativeRadical 2 F.top.ker) = chart23.space :=
    hR.trans BinaryHeisenbergEightNaturalHeads.radical14_space.symm
  have hRK : chart23.space ≤ chart40.space :=
    chart23.le_of_basis_mem _ (by decide +kernel)
  have hcard := F.heisenberg_rank_five_card_bounds hU hrank hH (Nat.card chart23.space)
    (by rw [hKC, chart40.card, chart23.card]; decide)
  exact F.heisenberg_unit_normalF_of_doubled_axis_envelopes hU hH
    chart40.space chart23.space hKC.symm hRK
    (F.radical_coordinate_le_derived chart23.space hRC)
    4 (by simpa only [chart23.card] using hcard.2)
    (by rw [chart23.card]; decide) hcard.1.le
    BinaryHeisenberg14AllJointAxes.all_axes N hnonab

end SymmetricSubgroupAsymptotics.BinaryPairFrame
