import SymmetricSubgroupAsymptotics.RDTNormalFSmallPairTopRankFive
import SymmetricSubgroupAsymptotics.RDTNormalFSixteenExcessOneRank
import SymmetricSubgroupAsymptotics.BinaryExcessOneAbelianization

/-! Direct excess-one adapter: full abelianization exponent and original
rank five are supplied by proved general binary theorems, not assumptions. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open MarkedC4 MarkedC4.RDTExcessStructure

variable {G : Subgroup (Equiv.Perm (Fin 16))}
    (F : BinaryPairFrame G (Fin 8)) [MulAction G (Fin 8)]
    [MulAction.IsPretransitive G (Fin 8)]
    [MulAction.IsPretransitive F.top.range (Fin 8)]
    (hact : ∀ (g : G) (i : Fin 8), g • i = F.top g i)

include hact in
/-- The SAME actual excess-one source and original denominator N. -/
theorem small_pair_top_excess_one_rank_preserving_unit
    (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin 16, ∃ g : G, g.val x = y)
    (hexcess : HasExcess G 16 1)
    (hnon : ¬ BinarySquareActionStructure.SquaresActTrivially (G := G) (X := Fin 8))
    (htop : Nat.card F.top.range ≤ 32)
    (htoprank : genRank F.top.range ≤ 3)
    (N : Subgroup G) [N.Normal]
    (hQrank : genRank (G ⧸ N) = 5)
    (hnonab : ¬ ∀ a b : G ⧸ N, a*b=b*a) :
    ∃ W : Subgroup (G ⧸ N), W.Normal ∧
      ActualNormalFMarkedPeel.commutatorLog W +
        ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
      ActualNormalFMarkedPeel.centralLog W ≤ 4 :=
  F.small_pair_top_rank_five_rank_preserving_unit hact hG hnon htop htoprank
    (degree_sixteen_excess_one_genRank_eq_five G hG htrans hexcess)
    (binary_excess_one_abelianization_exponent 16 G (by decide) hG htrans hexcess)
    N hQrank hnonab

end SymmetricSubgroupAsymptotics.BinaryPairFrame
