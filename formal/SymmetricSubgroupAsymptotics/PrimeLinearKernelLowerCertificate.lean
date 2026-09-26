import SymmetricSubgroupAsymptotics.PrimeLinearKernelCertificate

/-! Distinct displayed vectors in an actual finite linear kernel give
lower cardinality and dimension bounds. They complement the independent
decoder upper bounds without requiring a symbolic matrix-rank calculation.
Only actual kernel membership and injectivity of the displayed vectors
are used; no completeness of their list is assumed. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
    {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod p) V] [Module (ZMod p) W] [Finite V]

/-- Injective selected vectors give a cardinality lower bound on the
same actual kernel, even when other kernel vectors may exist. -/
theorem primeLinearMap_le_card_ker_of_injective_vectors (f : V →ₗ[ZMod p] W)
    (k : ℕ) (select : Fin k → V)
    (hmem : ∀ i, f (select i) = 0) (hinj : Function.Injective select) :
    k ≤ Nat.card f.ker := by
  let embed : Fin k → f.ker := fun i => ⟨select i, hmem i⟩
  have he : Function.Injective embed := by
    intro i j h
    exact hinj (congrArg Subtype.val h)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective embed he

/-- At least p^r distinct actual kernel vectors force dimension at
least r. The prime-power conversion uses the entire actual kernel. -/
theorem primeLinearMap_le_finrank_ker_of_injective_vectors (f : V →ₗ[ZMod p] W)
    (r : ℕ) (select : Fin (p ^ r) → V)
    (hmem : ∀ i, f (select i) = 0) (hinj : Function.Injective select) :
    r ≤ Module.finrank (ZMod p) f.ker := by
  have hc := primeLinearMap_le_card_ker_of_injective_vectors p f (p ^ r) select hmem hinj
  rw [primeLinearMap_card_ker p f] at hc
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hc

/-- A proved upper dimension bound and injective actual kernel witnesses
together give the exact dimension, with both directions explicit. -/
theorem primeLinearMap_finrank_ker_eq_of_injective_vectors (f : V →ₗ[ZMod p] W)
    (r : ℕ) (select : Fin (p ^ r) → V)
    (hmem : ∀ i, f (select i) = 0) (hinj : Function.Injective select)
    (hupper : Module.finrank (ZMod p) f.ker ≤ r) :
    Module.finrank (ZMod p) f.ker = r :=
  le_antisymm hupper
    (primeLinearMap_le_finrank_ker_of_injective_vectors p f r select hmem hinj)

end SymmetricSubgroupAsymptotics
