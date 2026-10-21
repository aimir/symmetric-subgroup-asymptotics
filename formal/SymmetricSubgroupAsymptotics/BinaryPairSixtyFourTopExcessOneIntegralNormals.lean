import SymmetricSubgroupAsymptotics.BinaryPairSixtyFourTopIntegralNormals
import SymmetricSubgroupAsymptotics.RDTNormalFSixteenExcessOneRank
import SymmetricSubgroupAsymptotics.BinaryExcessOneAbelianization

/-! No new exponent premise is needed for the actual excess-one source. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open MarkedC4 MarkedC4.RDTExcessStructure

variable {G : Subgroup (Equiv.Perm (Fin 16))}
    (F : BinaryPairFrame G (Fin 8)) [MulAction G (Fin 8)]
    [MulAction.IsPretransitive G (Fin 8)]
    (hact : ∀ (g : G) (i : Fin 8), g • i = F.top g i)

include hact in
theorem sixtyfour_pair_top_excess_one_proper_normal_integral_order_le_sixteen
    (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin 16, ∃ g : G, g.val x = y)
    (hexcess : HasExcess G 16 1)
    (hnon : ¬ BinarySquareActionStructure.SquaresActTrivially (G := G) (X := Fin 8))
    (htop : Nat.card F.top.range ≤ 64)
    (htoprank : genRank F.top.range ≤ 3)
    (E : Subgroup G) [E.Normal] (hproper : E ≠ ⊤) :
    normalIntegralCoinvariantOrder E ≤ 16 := by
  letI sixtyfourExcessIntegral_primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hexp := binary_excess_one_abelianization_exponent 16 G (by decide) hG htrans hexcess
  have hAb : Nat.card (Abelianization G) = 32 := by
    rw [pGroup_abelianization_card_eq_pow_genRank 2 hG hexp,
      degree_sixteen_excess_one_genRank_eq_five G hG htrans hexcess]
    decide
  have hTopAb : Nat.card (Abelianization F.top.range) ≤ 8 := by
    have hTopExp := abelianization_exponent_of_surjective F.top.rangeRestrict
      F.top.rangeRestrict_surjective 2 hexp
    rw [pGroup_abelianization_card_eq_pow_genRank 2 (F.top_isPGroup hG) hTopExp]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) htoprank
  exact F.sixtyfour_pair_top_proper_normal_integral_order_le_sixteen
    hact hG hnon htop hAb.le hTopAb E hproper

end SymmetricSubgroupAsymptotics.BinaryPairFrame
