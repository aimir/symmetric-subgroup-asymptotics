import SymmetricSubgroupAsymptotics.BinaryStructuredPolynomialBound

/-! A coordinate-wise order budget bounds the same original source and
its binary character rank. The embedding need not have full projections;
in particular, the bounds apply to every literal tail subgroup of a
carrier word, without replacing it by the whole direct product.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

theorem binaryCarrier_source_card_le_pow
    {ι : Type*} [Fintype ι] (A : ι → Type*) [∀ i, Group (A i)]
    [∀ i, Finite (A i)] {G : Type*} [Group G] [Finite G]
    (f : G →* ∀ i, A i) (hf : Function.Injective f)
    (a : ι → ℕ) (ha : ∀ i, Nat.card (A i) ≤ 2^(a i)) :
    Nat.card G ≤ 2^(∑ i, a i) := by
  calc
    _ ≤ Nat.card (∀ i, A i) := Nat.card_le_card_of_injective f hf
    _ = ∏ i, Nat.card (A i) := Nat.card_pi
    _ ≤ ∏ i, 2^(a i) := Finset.prod_le_prod
      (fun _ _ => Nat.zero_le _) (fun i _ => ha i)
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

theorem binaryCarrier_source_rank_le
    {ι : Type*} [Fintype ι] (A : ι → Type*) [∀ i, Group (A i)]
    [∀ i, Finite (A i)] {G : Type*} [Group G] [Finite G]
    (f : G →* ∀ i, A i) (hf : Function.Injective f)
    (a : ι → ℕ) (ha : ∀ i, Nat.card (A i) ≤ 2^(a i)) :
    binaryCharacterRank G ≤ ∑ i, a i :=
  binaryCharacterRank_le_of_card_le_pow G _
    (binaryCarrier_source_card_le_pow A f hf a ha)

/-- Every actual tail subgroup shares the coordinate order budget. -/
theorem binaryCarrier_subgroup_card_le_pow
    {ι : Type*} [Fintype ι] (A : ι → Type*) [∀ i, Group (A i)]
    [∀ i, Finite (A i)] (H : Subgroup (∀ i, A i))
    (a : ι → ℕ) (ha : ∀ i, Nat.card (A i) ≤ 2^(a i)) :
    Nat.card H ≤ 2^(∑ i, a i) :=
  binaryCarrier_source_card_le_pow A H.subtype Subtype.coe_injective a ha

/-- The shared alphabet constant and coordinate budgets control the
polynomial loss for this exact original tail subgroup. -/
theorem binaryCarrier_subgroup_polynomial_le
    {ι : Type*} [Fintype ι] (A : ι → Type*) [∀ i, Group (A i)]
    [∀ i, Finite (A i)] (H : Subgroup (∀ i, A i))
    (a : ι → ℕ) (ha : ∀ i, Nat.card (A i) ≤ 2^(a i))
    (Q : Type*) [Group Q] [Finite Q] (C : ℕ)
    (hC : binaryStructuredEpiConstant Q ≤ C) :
    binaryStructuredEpiConstant Q *
      (binaryCharacterRank H+2)^(binaryStructuredEpiConstant Q) ≤
        C*((∑ i, a i)+2)^C :=
  binaryStructured_polynomial_le_uniform Q _ _ C
    (binaryCarrier_source_rank_le A H.subtype Subtype.coe_injective a ha) hC

end SymmetricSubgroupAsymptotics
