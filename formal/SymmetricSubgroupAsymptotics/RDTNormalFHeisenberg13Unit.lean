import SymmetricSubgroupAsymptotics.RDTNormalFHeisenbergUnitAxisEnvelope
import SymmetricSubgroupAsymptotics.BinaryHeisenbergRankFiveCards
import SymmetricSubgroupAsymptotics.BinaryHeisenberg13AllJointAxes

/-! The retained K13 joint envelope also covers every original rank-five
extension at unit coefficient, including all nonabelian normal quotients.
No rank-six saturation or zero affine lift is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8))
open BinaryRegularEightNaturalRegistry (chart33 chart40)

theorem heisenberg13_unit_normalF_packet
    (hU : IsPGroup 2 U) (hrank : 5 ≤ MarkedC4.genRank U)
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (hK : F.kernelSpace = BinaryHeisenbergEightSquareCarry.K13)
    (hR : F.ambientAxis (primeRelativeRadical 2 F.top.ker) = BinaryHeisenbergEightSquareCarry.R13)
    (N : Subgroup U) [N.Normal]
    (hnonab : ¬ ∀ a b : U ⧸ N, a * b = b * a) :
    ∃ W : Subgroup (U ⧸ N), W.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog W +
        MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 4 := by
  have hKC : F.kernelSpace = chart33.space :=
    hK.trans BinaryHeisenbergEightNaturalHeads.kernel13_space.symm
  have hRC : F.ambientAxis (primeRelativeRadical 2 F.top.ker) = chart40.space :=
    hR.trans BinaryHeisenbergEightNaturalHeads.radical13_space.symm
  have hRK : chart40.space ≤ chart33.space :=
    chart40.le_of_basis_mem _ (by decide +kernel)
  have hcard := F.heisenberg_rank_five_card_bounds hU hrank hH (Nat.card chart40.space)
    (by rw [hKC, chart33.card, chart40.card]; decide)
  exact F.heisenberg_unit_normalF_of_doubled_axis_envelopes hU hH
    chart33.space chart40.space hKC.symm hRK
    (F.radical_coordinate_le_derived chart40.space hRC)
    16 (by simpa only [chart40.card] using hcard.2)
    (by rw [chart40.card]; decide) hcard.1.le
    BinaryHeisenberg13AllJointAxes.all_axes N hnonab

end SymmetricSubgroupAsymptotics.BinaryPairFrame
