import SymmetricSubgroupAsymptotics.ComponentOrderCubeOrdinaryNumerics
import SymmetricSubgroupAsymptotics.PrimitiveSocleBoundedComponentClassBound

/-! Original nonaffine index-form product actions with at least two
socle factors satisfy the ordinary half-degree bound whenever the
existing component ORDER cube holds. All subgroups use the same
original point degree; the full original socle and quotient are kept. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subgroup_genRank_half_degree_of_product_order_cube
    (D : NonaffineData G X) (b : ℕ) (hb : 4 ≤ b) (hk : 2 ≤ D.factorCount)
    (hbase : (Nat.card D.Simple*Nat.card (Outer D.Simple))^3 ≤ 5^(b-1))
    (K : Subgroup D.Simple) (hindex : b ≤ K.index)
    (hdegree : Nat.card X=K.index^D.factorCount) (H : Subgroup G) :
    2*MarkedC4.genRank H ≤ Nat.card X := by
  have hc := ComponentOrderCubeOrdinaryNumerics.genRank_half_degree_of_order_cube H
    (Nat.card D.Simple*Nat.card (Outer D.Simple)) b D.factorCount hb hk hbase
    (H.card_le_card_group.trans D.card_le_simple_outer_wreath)
  exact hc.trans ((Nat.pow_le_pow_left hindex D.factorCount).trans_eq hdegree.symm)

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
