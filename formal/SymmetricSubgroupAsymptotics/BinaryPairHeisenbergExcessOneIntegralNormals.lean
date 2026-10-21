import SymmetricSubgroupAsymptotics.BinaryPairHeisenbergIntegralNormals
import SymmetricSubgroupAsymptotics.RDTNormalFSixteenExcessOneRank
import SymmetricSubgroupAsymptotics.BinaryExcessOneAbelianization

/-! The actual degree-sixteen excess-one profile supplies the original
abelianization order used by the integral Heisenberg-top theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open MarkedC4 MarkedC4.RDTExcessStructure

variable {G : Subgroup (Equiv.Perm (Fin 16))} (F : BinaryPairFrame G (Fin 8))

theorem heisenberg_pair_top_excess_one_proper_normal_integral_order_le_sixteen
    (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin 16, ∃ g : G, g.val x = y)
    (hexcess : HasExcess G 16 1)
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (E : Subgroup G) [E.Normal] (hproper : E ≠ ⊤) :
    normalIntegralCoinvariantOrder E ≤ 16 := by
  letI heisenbergExcessIntegral_primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAb : Nat.card (Abelianization G) = 32 := by
    rw [pGroup_abelianization_card_eq_pow_genRank 2 hG
      (binary_excess_one_abelianization_exponent 16 G (by decide) hG htrans hexcess),
      degree_sixteen_excess_one_genRank_eq_five G hG htrans hexcess]
    decide
  exact F.heisenberg_pair_top_proper_normal_integral_order_le_sixteen
    hG hH hAb.le E hproper

end SymmetricSubgroupAsymptotics.BinaryPairFrame
