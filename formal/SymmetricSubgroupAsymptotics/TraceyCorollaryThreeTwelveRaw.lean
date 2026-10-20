import SymmetricSubgroupAsymptotics.TraceySolubleOrbitInducedInput

/-! Raw orbit geometry from Tracey, Corollary 3.12 (printed p.17), with
`a ≥ 3` from its preceding nonabelian PSL₂(p) construction. This is a
published structural input, not a module-capacity or numerical conclusion. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

/-- The actual group has no soluble subgroup transitive on its points. -/
def HasNoSolubleTransitiveSubgroup (G X : Type) [Group G] [MulAction G X] : Prop :=
  ∀ N : Subgroup G, IsSolvable N → ¬ MulAction.IsPretransitive N X

/-- Literal binomial orbit data. The index equivalence records the full
orbit partition, so the displayed multiplicities cannot omit any orbit. -/
def TraceyCorollaryThreeTwelveRawInput : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] [MulAction.IsPretransitive G X],
    HasNoSolubleTransitiveSubgroup G X →
    ∀ m : ℕ, Nat.card X = 3 * 2 ^ m →
    ∃ (a e t₁ t : ℕ) (N : Subgroup G),
      3 ≤ a ∧ 1 ≤ e ∧ t₁ ≤ t ∧ m = e * a + t ∧
      Nat.Prime (2 ^ a - 1) ∧ IsSolvable N ∧
      Nat.card (MulAction.orbitRel.Quotient N X) = 2 ^ (e + t₁) ∧
      ∃ index : MulAction.orbitRel.Quotient N X ≃
        (Σ k : Fin (e + 1), Fin (e.choose k.val * 2 ^ t₁)),
        ∀ o : MulAction.orbitRel.Quotient N X,
          Nat.card o.orbit =
            3 * (2 ^ a - 1) ^ (index o).1.val * 2 ^ (t - t₁)

end SymmetricSubgroupAsymptotics
