import SymmetricSubgroupAsymptotics.RDTNormalFHeisenbergAxisEnvelope
import SymmetricSubgroupAsymptotics.BinaryHeisenbergRankSixCards
import SymmetricSubgroupAsymptotics.BinaryHeisenberg12AllJointAxes

/-! Every original rank-six Heisenberg K12 extension satisfies the normal-F
packet for every literal nonabelian normal quotient, including nonzero top
image. Its actual correlated kernel and arbitrary lift offsets are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8)) [MulAction.IsPretransitive U X]
open BinaryRegularEightNaturalRegistry (chart45 chart33)

theorem heisenberg12_five_quarters_normalF_packet
    (hU : IsPGroup 2 U) (hrank : 6 ≤ MarkedC4.genRank U)
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (hK : F.kernelSpace = BinaryHeisenbergEightSquareCarry.K12)
    (hR : F.ambientAxis (primeRelativeRadical 2 F.top.ker) = BinaryHeisenbergEightSquareCarry.R12)
    (N : Subgroup U) [N.Normal]
    (hnonab : ¬ ∀ a b : U ⧸ N, a * b = b * a) :
    ∃ V : Subgroup (U ⧸ N), V.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog V +
        (5 / 4 : ℝ) * MarkedC4.ActualNormalFMarkedPeel.centralLog V ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog V ≤ 4 := by
  have hKC : F.kernelSpace = chart45.space :=
    hK.trans BinaryHeisenbergEightNaturalHeads.kernel12_space.symm
  have hRC : F.ambientAxis (primeRelativeRadical 2 F.top.ker) = chart33.space :=
    hR.trans BinaryHeisenbergEightNaturalHeads.radical12_space.symm
  have hRK : chart33.space ≤ chart45.space :=
    chart33.le_of_basis_mem _ (by decide +kernel)
  have hcard := F.heisenberg_rank_six_card_data hU hrank hH (Nat.card chart33.space)
    (by rw [hKC, chart45.card, chart33.card]; decide)
  exact F.heisenberg_normalF_of_axis_envelopes hH chart45.space chart33.space hKC.symm hRK
    (F.heisenberg_rank_six_radical_coordinate_le_derived hU hrank hH chart33.space hRC)
    64 (hcard.2.trans (by rw [chart33.card]; decide))
    (by rw [chart33.card]; decide) hcard.1.le
    BinaryHeisenberg12AllJointAxes.all_axes N hnonab

end SymmetricSubgroupAsymptotics.BinaryPairFrame
