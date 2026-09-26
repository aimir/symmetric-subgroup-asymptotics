import SymmetricSubgroupAsymptotics.BinaryCarrierWord
import SymmetricSubgroupAsymptotics.BinaryStructuredOrderConstant

/-! Original order budgets for a complete word of bounded carriers.
The same cap controls the full product, every correlated subgroup and
every literal normal quotient of an original factor.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierWord

/-- A bound on each original factor, independent of its normal-axis choice. -/
def OrderBound : List Factor → ℕ → Prop
  | [], _ => True
  | A :: w, a => Nat.card A.Carrier ≤ 2^a ∧ OrderBound w a

theorem product_card_le_orderBound (w : List Factor) (a : ℕ)
    (ha : OrderBound w a) : Nat.card (Product w) ≤ 2^(a*w.length) := by
  induction w with
  | nil => simp [Product]
  | cons A w ih =>
      change Nat.card (A.Carrier × Product w) ≤ 2^(a*(w.length+1))
      rw [Nat.card_prod, Nat.mul_add, Nat.mul_one, pow_add]
      exact (Nat.mul_le_mul ha.1 (ih ha.2)).trans_eq (Nat.mul_comm _ _)

/-- No projection hypothesis is required for the order of a correlated tail. -/
theorem subgroup_card_le_orderBound (w : List Factor) (a : ℕ)
    (ha : OrderBound w a) (H : Subgroup (Product w)) :
    Nat.card H ≤ 2^(a*w.length) :=
  (Nat.card_le_card_of_injective H.subtype Subtype.val_injective).trans
    (product_card_le_orderBound w a ha)

theorem factor_card_le_orderBound {w : List Factor} {A : Factor}
    (i : Slot w A) (a : ℕ) (ha : OrderBound w a) : Nat.card A.Carrier ≤ 2^a := by
  induction i with
  | head => exact ha.1
  | tail i ih => exact ih ha.2

/-- Every axis in every original coordinate inherits the same proved constant. -/
theorem quotient_constant_le_orderBound {w : List Factor} {A : Factor}
    (i : Slot w A) (a : ℕ) (ha : OrderBound w a)
    (N : Subgroup A.Carrier) [N.Normal] :
    binaryStructuredEpiConstant (A.Carrier ⧸ N) ≤ binaryStructuredOrderConstant a :=
  binaryStructuredQuotientConstant_le_orderConstant A.Carrier N a
    (factor_card_le_orderBound i a ha)

end SymmetricSubgroupAsymptotics.BinaryCarrierWord
