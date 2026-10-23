import SymmetricSubgroupAsymptotics.PrimitiveSocleWeakClassicalOrderCubeClassBound

/-! A finite field/rank frontier for the actual weak-star classical
routes. This exposes unproved small parameters rather than silently
using a stronger least-index estimate. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.WeakClassicalOrderCubeNumerics

def SmallParameters (q t : ℕ) : Prop :=
  (t=2 ∧ q≤22) ∨ (t=3 ∧ q≤7) ∨ (t=4 ∧ q≤4) ∨ (t=5 ∧ q≤3) ∨
    (6≤t ∧ t≤9 ∧ q=2)

theorem smallParameters_of_not_capacity (q t : ℕ) (hq : 2≤q) (ht : 2≤t)
    (hc : ¬Capacity q t) : SmallParameters q t := by
  unfold Capacity at hc
  unfold SmallParameters
  omega

end SymmetricSubgroupAsymptotics.WeakClassicalOrderCubeNumerics

namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open WeakClassicalOrderCubeNumerics
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subgroup_class_cube_or_typeC_finite_parameters
    (D : NonaffineData G X) (r : ℕ) (hr : 2≤r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.C r q) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card X-1) ∨
      (r=2 ∧ q.order≤255) ∨ (3≤r ∧ SmallParameters q.order (r-1)) := by
  by_cases htwo : r=2
  · subst r
    by_cases hq : 256≤q.order
    · exact Or.inl (D.subgroup_class_cube_le_of_typeC_rank_two_capacity q hq e H)
    · exact Or.inr (Or.inl ⟨rfl, by omega⟩)
  · by_cases hc : Capacity q.order (r-1)
    · exact Or.inl (D.subgroup_class_cube_le_of_typeC_capacity r (by omega) q e hc H)
    · have hq : 2≤q.order := q.prime_isPrime.two_le.trans
        (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
      exact Or.inr (Or.inr ⟨by omega,
        smallParameters_of_not_capacity q.order (r-1) hq (by omega) hc⟩)

theorem NonaffineData.subgroup_class_cube_or_typeB_finite_parameters
    (D : NonaffineData G X) (r : ℕ) (hr : 3≤r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.B r q) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card X-1) ∨ SmallParameters q.order (r-1) := by
  by_cases hc : Capacity q.order (r-1)
  · exact Or.inl (D.subgroup_class_cube_le_of_typeB_capacity r hr q e hc H)
  · have hq : 2≤q.order := q.prime_isPrime.two_le.trans
      (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
    exact Or.inr (smallParameters_of_not_capacity q.order (r-1) hq (by omega) hc)

theorem NonaffineData.subgroup_class_cube_or_typeD_finite_parameters
    (D : NonaffineData G X) (r : ℕ) (hr : 4≤r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.D r q) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card X-1) ∨ SmallParameters q.order (r-1) := by
  by_cases hc : Capacity q.order (r-1)
  · exact Or.inl (D.subgroup_class_cube_le_of_typeD_capacity r hr q e hc H)
  · have hq : 2≤q.order := q.prime_isPrime.two_le.trans
      (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
    exact Or.inr (smallParameters_of_not_capacity q.order (r-1) hq (by omega) hc)

theorem NonaffineData.subgroup_class_cube_or_typeTwistedD_finite_parameters
    (D : NonaffineData G X) (r : ℕ) (hr : 4≤r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.TwistedD r q) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card X-1) ∨ SmallParameters q.order (r-2) := by
  by_cases hc : Capacity q.order (r-2)
  · exact Or.inl (D.subgroup_class_cube_le_of_typeTwistedD_capacity r hr q e hc H)
  · have hq : 2≤q.order := q.prime_isPrime.two_le.trans
      (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
    exact Or.inr (smallParameters_of_not_capacity q.order (r-2) hq (by omega) hc)

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
