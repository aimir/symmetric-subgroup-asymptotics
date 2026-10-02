import SymmetricSubgroupAsymptotics.ChiefTernaryWeights
import Mathlib.GroupTheory.GroupAction.Primitive

/-! The reusable statement of the primitive ternary three-tenths bound. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- Strict primitive composition-weight density in the form needed at a
binary top.  A weak inequality suffices for the high-action exclusion. -/
def PrimitiveTernaryThreeTenthsWeightBound : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X],
    4 ≤ Nat.card X → Nat.card X ≠ 9 →
      ∀ c : ActualChiefSeries G,
        10 * actualChiefSeriesTernaryWeight c ≤ 3 * Nat.card X

end SymmetricSubgroupAsymptotics

end
