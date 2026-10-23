import SymmetricSubgroupAsymptotics.LogSquareOrderClassNumerics
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.ConjFinite

/-! The logarithmic-square order ceiling pays the class-count cube for
every actual subgroup. No class-count monotonicity is used. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.LogSquareOrderSubgroupClassBound

theorem subgroup_class_cube_le {G : Type*} [Group G] [Finite G]
    (n : ℕ) (hn : 1024 ≤ n) (horder : Nat.card G ≤ n^(4*Nat.log 2 n+2))
    (H : Subgroup G) : Nat.card (ConjClasses H)^3 ≤ 5^(n-1) := by
  have hc : Nat.card (ConjClasses H) ≤ n^(4*Nat.log 2 n+2) :=
    (Nat.card_le_card_of_surjective (@ConjClasses.mk H _) ConjClasses.mk_surjective).trans
      (H.card_le_card_group.trans horder)
  exact (Nat.pow_le_pow_left hc 3).trans
    (LogSquareOrderClassNumerics.order_cube_le_garonziMaroti n hn)

end SymmetricSubgroupAsymptotics.LogSquareOrderSubgroupClassBound
