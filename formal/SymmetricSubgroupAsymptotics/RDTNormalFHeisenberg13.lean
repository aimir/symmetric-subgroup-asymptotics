import SymmetricSubgroupAsymptotics.RDTNormalFHeisenbergAxisEnvelope
import SymmetricSubgroupAsymptotics.BinaryHeisenbergRankSixCards
import SymmetricSubgroupAsymptotics.BinaryHeisenberg13AllJointAxes

/-! Every original rank-six Heisenberg K13 extension satisfies the normal-F
packet for every literal nonabelian normal quotient, including nonzero top
image. Its actual correlated kernel and arbitrary lift offsets are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8)) [MulAction.IsPretransitive U X]
open BinaryRegularEightNaturalRegistry (chart33 chart40)

theorem heisenberg13_five_quarters_normalF_packet
    (hU : IsPGroup 2 U) (hrank : 6 ≤ MarkedC4.genRank U)
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (hK : F.kernelSpace = BinaryHeisenbergEightSquareCarry.K13)
    (hR : F.ambientAxis (primeRelativeRadical 2 F.top.ker) = BinaryHeisenbergEightSquareCarry.R13)
    (N : Subgroup U) [N.Normal]
    (hnonab : ¬ ∀ a b : U ⧸ N, a * b = b * a) :
    ∃ V : Subgroup (U ⧸ N), V.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog V +
        (5 / 4 : ℝ) * MarkedC4.ActualNormalFMarkedPeel.centralLog V ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog V ≤ 4 := by
  have hKC : F.kernelSpace = chart33.space :=
    hK.trans BinaryHeisenbergEightNaturalHeads.kernel13_space.symm
  have hRC : F.ambientAxis (primeRelativeRadical 2 F.top.ker) = chart40.space :=
    hR.trans BinaryHeisenbergEightNaturalHeads.radical13_space.symm
  have hRK : chart40.space ≤ chart33.space :=
    chart40.le_of_basis_mem _ (by decide +kernel)
  have hcard := F.heisenberg_rank_six_card_data hU hrank hH (Nat.card chart40.space)
    (by rw [hKC, chart33.card, chart40.card]; decide)
  exact F.heisenberg_normalF_of_axis_envelopes hH chart33.space chart40.space hKC.symm hRK
    (F.heisenberg_rank_six_radical_coordinate_le_derived hU hrank hH chart40.space hRC)
    16 (hcard.2.trans (by rw [chart40.card]; decide))
    (by rw [chart40.card]; decide) hcard.1.le
    BinaryHeisenberg13AllJointAxes.all_axes N hnonab

end SymmetricSubgroupAsymptotics.BinaryPairFrame
