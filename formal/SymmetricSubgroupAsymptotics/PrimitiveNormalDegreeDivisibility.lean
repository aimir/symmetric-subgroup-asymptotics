import SymmetricSubgroupAsymptotics.PrimitiveSocleAffineAlternative
import Mathlib.GroupTheory.GroupAction.Quotient

/-! An actual normal subgroup of a faithful primitive action is either
trivial or has order divisible by the actual point degree. In particular
an odd-order normal subgroup cannot survive at even primitive degree.
No group-recognition or catalogue premise is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveNormalDegreeDivisibility

variable {G X : Type} [Group G] [Finite G] [Finite X] [Nonempty X]
    [MulAction G X] [FaithfulSMul G X] [MulAction.IsPreprimitive G X]

theorem eq_bot_of_degree_not_dvd_card (N : Subgroup G) [N.Normal]
    (hnot : ¬Nat.card X ∣ Nat.card N) : N = ⊥ := by
  by_contra hne
  letI : MulAction.IsPretransitive N X :=
    PrimitiveSocleONanScottHelpers.normal_transitive_of_ne_bot N hne
  let x : X := Classical.choice inferInstance
  have hdiv : Nat.card X ∣ Nat.card N := by
    rw [←MulAction.index_stabilizer_of_transitive N x]
    exact Subgroup.index_dvd_card _
  exact hnot hdiv

theorem eq_bot_of_degree_divisor_not_dvd_card (N : Subgroup G) [N.Normal]
    (p : ℕ) (hp : p ∣ Nat.card X) (hnot : ¬p ∣ Nat.card N) : N = ⊥ :=
  eq_bot_of_degree_not_dvd_card (X := X) N (fun h => hnot (hp.trans h))

end SymmetricSubgroupAsymptotics.PrimitiveNormalDegreeDivisibility
