import SymmetricSubgroupAsymptotics.BinaryPairRegularIntegralNormals
import SymmetricSubgroupAsymptotics.RDTNormalFSixteenExcessOneRank
import SymmetricSubgroupAsymptotics.BinaryExcessOneAbelianization

/-! The regular-top integral theorem instantiated from the original
sixteen-point excess-one profile. The exponent is proved internally. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open MarkedC4 MarkedC4.RDTExcessStructure

variable {G : Subgroup (Equiv.Perm (Fin 16))} (F : BinaryPairFrame G (Fin 8))

theorem regular_pair_top_excess_one_proper_normal_integral_order_le_sixteen
    (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin 16, ∃ g : G, g.val x = y)
    (hexcess : HasExcess G 16 1)
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (htoprank : genRank F.top.range ≤ 3)
    (E : Subgroup G) [E.Normal] (hproper : E ≠ ⊤) :
    normalIntegralCoinvariantOrder E ≤ 16 := by
  letI regularExcessIntegral_originalTransitive : MulAction.IsPretransitive G (Fin 16) :=
    ⟨htrans⟩
  letI regularExcessIntegral_topTransitive : MulAction.IsPretransitive F.top.range (Fin 8) :=
    F.top_pretransitive
  exact F.regular_pair_top_proper_normal_integral_order_le_sixteen hG hH htoprank
    (degree_sixteen_excess_one_genRank_eq_five G hG htrans hexcess)
    (binary_excess_one_abelianization_exponent 16 G (by decide) hG htrans hexcess)
    E hproper

end SymmetricSubgroupAsymptotics.BinaryPairFrame
