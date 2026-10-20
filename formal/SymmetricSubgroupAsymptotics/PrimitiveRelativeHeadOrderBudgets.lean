import SymmetricSubgroupAsymptotics.PrimitiveRelativeHeadSocle
import Mathlib.GroupTheory.GroupAction.Quotient

/-! Shared actual-order budgets for primitive relative heads. These lemmas
separate the semantic action/socle proof from any bounded catalogue row. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]

/-- Even before a socle is recognized, every actual normal relative head
is paid by the same original ambient prime valuation. -/
theorem primeRelativeHead_le_groupFactorization
    {G : Type} [Group G] [Finite G] (N : Subgroup G) [N.Normal] :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) ≤ (Nat.card G).factorization p := by
  have hdvd : p^Module.finrank (ZMod p) (primeRelativeCharacters p N)∣Nat.card G :=
    ((pow_dvd_pow p (Submodule.finrank_le (primeRelativeCharacters p N))).trans
      (primeCharacters_pow_finrank_dvd_card p N)).trans
        (Subgroup.card_subgroup_dvd_card N)
  have h := (Nat.factorization_le_iff_dvd
    (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) Nat.card_pos.ne').mpr hdvd p
  simpa only [Nat.factorization_pow_self (Fact.out : p.Prime)] using h

/-- Transitivity of the specified actual normal subgroup forces the action
degree to divide that subgroup's order. -/
theorem degree_dvd_card_of_transitive_normal
    {G X : Type} [Group G] [Finite G] [Finite X] [Nonempty X] [MulAction G X]
    (E : Subgroup G) [MulAction.IsPretransitive E X] : Nat.card X∣Nat.card E := by
  let x : X := Classical.choice inferInstance
  rw [←MulAction.index_stabilizer_of_transitive E x]
  exact Subgroup.index_dvd_card _

/-- A minimal self-centralizing transitive subgroup removes both its own
head and the prime part of the action degree from the ambient order budget. -/
theorem primeRelativeHead_add_degreeFactorization_le_groupFactorization
    {G X : Type} [Group G] [Finite G] [Finite X] [Nontrivial X] [MulAction G X]
    [MulAction.IsPreprimitive G X]
    (E : Subgroup G) [E.Normal] [MulAction.IsPretransitive E X]
    (hminimal : ∀ B : Subgroup G,B.Normal → B≤E → B=⊥ ∨ B=E)
    (hself : ∀ x : G,(∀ e : E,x*(e : G)=(e : G)*x) → x∈E)
    (hdegree : Nat.card X≠p) (N : Subgroup G) [N.Normal] :
    Module.finrank (ZMod p) (primeRelativeCharacters p N)+(Nat.card X).factorization p ≤
      (Nat.card G).factorization p := by
  have hzero := primeRelativeHead_minimalSelfCentralizing_eq_zero_of_primitive
    p E hminimal hself hdegree
  have hhead := primeRelativeHead_le_quotientFactorization_of_minimalHeadZero
    p E hminimal hself hzero N
  have hdiv := degree_dvd_card_of_transitive_normal (X := X) E
  have hdeg : (Nat.card X).factorization p ≤ (Nat.card E).factorization p :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr hdiv p
  have hfactor : (Nat.card G).factorization p=
      (Nat.card (G⧸E)).factorization p+(Nat.card E).factorization p := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup E,
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
    rfl
  omega

end SymmetricSubgroupAsymptotics
