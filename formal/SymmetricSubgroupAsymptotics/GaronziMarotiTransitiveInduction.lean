import SymmetricSubgroupAsymptotics.GaronziMarotiIntransitiveReduction

/-! Strong induction eliminates the intransitive branch at every degree.
The remaining input is exactly the transitive GM cube on the SAME
original finite permutation subgroup. No primitive or imprimitive case
is asserted, and no smaller-degree GM input remains in the conclusion. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.GaronziMarotiTransitiveInduction
open GaronziMarotiIntransitiveReduction

theorem class_cube_le_of_transitive
    (hTransitive : ∀ n : ℕ, 4 ≤ n → ∀ L : Subgroup (Equiv.Perm (Fin n)),
      MulAction.IsPretransitive L (Fin n) →
        Nat.card (ConjClasses L)^3 ≤ 5^(n-1)) :
    ∀ n : ℕ, 4 ≤ n → ∀ L : Subgroup (Equiv.Perm (Fin n)),
      Nat.card (ConjClasses L)^3 ≤ 5^(n-1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn L
    by_cases ht : MulAction.IsPretransitive L (Fin n)
    · exact hTransitive n hn L ht
    · have hsmaller : ∀ m : ℕ, m < Nat.card (Fin n) → 4 ≤ m →
          ∀ T : Subgroup (Equiv.Perm (Fin m)),
            Nat.card (ConjClasses T)^3 ≤ 5^(m-1) := by
        intro m hm h4 T
        exact ih m (by simpa only [Nat.card_fin] using hm) h4 T
      simpa only [Nat.card_fin] using
        intransitive_step (G := L) (X := Fin n) ht
          (by simpa only [Nat.card_fin] using hn) hsmaller

theorem faithful_action_class_cube_le_of_transitive
    (hTransitive : ∀ n : ℕ, 4 ≤ n → ∀ L : Subgroup (Equiv.Perm (Fin n)),
      MulAction.IsPretransitive L (Fin n) →
        Nat.card (ConjClasses L)^3 ≤ 5^(n-1))
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (hn : 4 ≤ Nat.card X) :
    Nat.card (ConjClasses G)^3 ≤ 5^(Nat.card X-1) :=
  class_cube_le_of_finite_permutation_bound G X _
    (class_cube_le_of_transitive hTransitive (Nat.card X) hn)

end SymmetricSubgroupAsymptotics.GaronziMarotiTransitiveInduction
