import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Linarith

/-! A literal normal with nonzero top image pays at least two copies of
its SAME kernel intersection. Normality is unnecessary for the cardinal
statement itself. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {G : Type*} [Group G] [Finite G]

theorem two_mul_inf_card_le_of_not_le (K N : Subgroup G) (hN : ¬ N ≤ K) :
    2 * Nat.card (K ⊓ N : Subgroup G) ≤ Nat.card N := by
  let A := K ⊓ N
  let B := A.subgroupOf N
  have hB : B ≠ ⊤ := by
    intro he
    apply hN
    intro x hx
    have hm : (⟨x, hx⟩ : N) ∈ B := by rw [he]; trivial
    exact hm.1
  have hc : Nat.card B = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show A ≤ N from inf_le_right)).toEquiv
  have hi := B.one_lt_index_of_ne_top hB
  have hf := B.card_mul_index
  rw [hc] at hf
  change 2 * Nat.card A ≤ Nat.card N
  nlinarith

end SymmetricSubgroupAsymptotics
