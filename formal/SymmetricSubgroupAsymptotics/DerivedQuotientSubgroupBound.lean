import SymmetricSubgroupAsymptotics.DerivedQuotientExactCard
import Mathlib.Tactic.Linarith

/-! The actual subgroup retained in the normal and in the derived group
pays the derived-quotient order. No unrelated denominator is substituted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {G : Type*} [Group G] [Finite G]
theorem quotient_derived_card_le_of_subgroup
    (N B : Subgroup G) [N.Normal] (hBN : B ≤ N) (hBD : B ≤ commutator G)
    (d : ℕ) (hd : Nat.card (commutator G) ≤ Nat.card B * d) :
    Nat.card (commutator (G ⧸ N)) ≤ d := by
  have hle : B ≤ N ⊓ commutator G := le_inf hBN hBD
  have hc := Nat.card_le_card_of_injective (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)
  have he := quotient_derived_card_mul_intersection N
  have hp : 0 < Nat.card B := Nat.card_pos
  nlinarith
end SymmetricSubgroupAsymptotics
