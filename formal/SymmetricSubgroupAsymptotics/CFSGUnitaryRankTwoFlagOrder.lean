import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoUpperFlag
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperCardinality
import SymmetricSubgroupAsymptotics.CFSGKernelFlagProductCard
import SymmetricSubgroupAsymptotics.CFSGSubgroupProductInside

/-! The actual original rank-two quotient contains a flag subgroup
whose product with the opposite q^3 group has full product cardinality.
This also proves injectivity of both unipotent images, using the
literal flag kernel containment rather than a centre formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedAUpperUnipotent

theorem rankTwoUpperSubgroup_card (q : CFSG.PrimePower) :
    Nat.card (rankTwoUpperSubgroup q) = q.order ^ 3 := by
  have hc : Nat.card (rankTwoUpperSubgroup q) = Nat.card (naturalUnipotent 2 q) :=
    Nat.card_congr ((naturalUnipotent 2 q).subgroupOfEquivOfLe
      (show naturalUnipotent 2 q ≤ naturalFixed 2 q from inf_le_right)).toEquiv
  exact hc.trans (naturalUnipotent_card q 2)

theorem rankTwoOppositeSubgroup_card (q : CFSG.PrimePower) :
    Nat.card (rankTwoOppositeSubgroup q) = q.order ^ 3 := by
  change Nat.card ((rankTwoUpperSubgroup q).map
    (MulAut.conj (reversalFixed q 2)).toMonoidHom) = _
  rw [Subgroup.card_map_of_injective (MulAut.conj (reversalFixed q 2)).injective,
    rankTwoUpperSubgroup_card]

theorem rankTwoProjectiveUpper_card (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    Nat.card ((rankTwoUpperSubgroup q).map (rankTwoProjectiveCover q hq)) = q.order ^ 3 := by
  have hc := CFSGKernelFlagProductCard.card_image (rankTwoProjectiveCover q hq)
    (rankTwoUpperFlag q) (rankTwoOppositeSubgroup q) (rankTwoOpposite_inf_flag q)
    (rankTwoProjectiveCover_kernel_le_flag q hq)
  have he := CFSGSubgroupProductInside.map_conjugate_card (rankTwoProjectiveCover q hq)
    (rankTwoUpperSubgroup q) (reversalFixed q 2)
  change Nat.card ((rankTwoOppositeSubgroup q).map (rankTwoProjectiveCover q hq)) = _ at he
  exact he.symm.trans (hc.trans (rankTwoOppositeSubgroup_card q))

theorem rankTwoProjectiveFlag_order_bound (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    q.order ^ 3 * Nat.card ((rankTwoUpperFlag q).map (rankTwoProjectiveCover q hq)) ≤
      Nat.card (CFSG.Models.TwistedA 2 q) := by
  letI : Finite (CFSG.Models.TwistedA 2 q) :=
    Finite.of_surjective (rankTwoProjectiveCover q hq) (rankTwoProjectiveCover_surjective q hq)
  have hh := CFSGKernelFlagProductCard.card_product_le (rankTwoProjectiveCover q hq)
    (rankTwoUpperFlag q) (rankTwoOppositeSubgroup q) (rankTwoOpposite_inf_flag q)
    (rankTwoProjectiveCover_kernel_le_flag q hq)
  rwa [rankTwoOppositeSubgroup_card] at hh

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
