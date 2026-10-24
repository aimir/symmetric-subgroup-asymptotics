import SymmetricSubgroupAsymptotics.CFSGConjugacyMinimumIndexBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleModelClassCubeSquareClassBound
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawChart
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex

/-! A family-independent class-equation capacity test on the literal
simple model. Actual order, outer order, proper index and least-index
square estimates are combined before the original primitive consumer.
Every original subnormal subgroup and degree witness is retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subnormal_class_cube_le_of_model_class_equation_budget
    (D : NonaffineData G X) (T : Type) [Group T] [Finite T]
    (e : D.Simple ≃* T) (b N O : ℕ) (hb : 3 ≤ b)
    (hi : ∀ K : Subgroup T, K ≠ ⊤ → b ≤ K.index)
    (hc : Nat.card T ≤ N) (ho : Nat.card (Outer T) ≤ O)
    (hs : ∀ ell, LeastProperIndex T ell → ell^2 < Nat.card T)
    (hbudget : ((N / b + 1) * O)^3 ≤ 5^(b-1))
    (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup T := e.symm.isSimpleGroup
  have hcenterless := (isCenterless_congr e).mp
    (centerless_of_nonabelian_simple D.Simple D.noncommutative)
  have hz : Subgroup.center T = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    exact Subgroup.mem_bot.mpr (hcenterless x (fun y => (Subgroup.mem_center_iff.mp hx y).symm))
  have hclass : Nat.card (ConjClasses T) ≤ N / b + 1 :=
    (CFSGConjugacyMinimumIndexBound.class_card_le_div_add_one b (by omega) hz hi).trans
      (Nat.add_le_add_right (Nat.div_le_div_right hc) 1)
  refine D.subnormal_class_cube_le_of_model_capacity T e b hb hi
    ((Nat.pow_le_pow_left (Nat.mul_le_mul hclass ho) 3).trans hbudget) ?_ H hH
  obtain ⟨ell, hell⟩ := exists_leastProperIndex T
  obtain ⟨K, hK, he⟩ := hell.1
  exact (Nat.pow_le_pow_left ((hi K hK).trans_eq he) 2).trans (hs ell hell).le

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
