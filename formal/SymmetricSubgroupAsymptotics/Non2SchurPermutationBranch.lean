import SymmetricSubgroupAsymptotics.Non2SchurBranchAssignment
import SymmetricSubgroupAsymptotics.Non2SchurPermutationSection

/-!
# Schur branch assignment for an actual permutation section

This is the structural interface used by the coupled-socle proposition.  An
actual surjective permutation-section map supplies both the physical carrier
bound and the pullback of the mixed carrier to the original permutation
module.  The remaining nonfaithful inputs are only local head capacities on
the literal orbits of the selected simple row kernel.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical MonoidAlgebra
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics

variable {B X A : Type} [Group B] [Finite B] [Finite X] [MulAction B X]
    [AddCommGroup A] [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]

omit [Finite B] [FiniteDimensional (ZMod 2) A] in
/-- The target dimension of a surjective quotient of a permutation
subrepresentation is at most the original permutation degree. -/
theorem permutationSection_finrank_le_card
    (sigma : Representation (ZMod 2) B A)
    (M : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) B X))
    (q : M.toRepresentation.IntertwiningMap sigma)
    (hq : Function.Surjective q) :
    Module.finrank (ZMod 2) A ≤ Nat.card X := by
  calc
    Module.finrank (ZMod 2) A ≤ Module.finrank (ZMod 2) M.toSubmodule :=
      LinearMap.finrank_le_finrank_of_surjective hq
    _ ≤ Module.finrank (ZMod 2) (X → ZMod 2) :=
      Submodule.finrank_le M.toSubmodule
    _ = Nat.card X := by
      rw [Module.finrank_pi, Fintype.card_eq_nat_card]

/-- Actual permutation-section branch assignment.  Physical size and orbit
filtration are proved internally; only the local transitive head estimates
and the faithful-image alternatives remain as inputs. -/
theorem Non2SchurStructuralBranch.of_permutationSection_orbit_caps
    (sigma : Representation (ZMod 2) B A)
    (S : Submodule (ZMod 2)[B] sigma.asModule)
    [IsSimpleModule (ZMod 2)[B] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S)
    (M : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) B X))
    (qmap : M.toRepresentation.IntertwiningMap sigma)
    (hqmap : Function.Surjective qmap)
    (ht : 32 * Module.finrank (ZMod 2) sigma.invariants ≤
      11 * Nat.card X)
    (cap : MulAction.orbitRel.Quotient
      (schurSimpleActionKernel sigma S) X → ℕ)
    (hcap : ∀ (o : MulAction.orbitRel.Quotient
        (schurSimpleActionKernel sigma S) X)
      (T : Subrepresentation (permutationFunctionRepresentation (ZMod 2)
        (schurSimpleActionKernel sigma S) o.orbit)),
      Module.finrank (ZMod 2) (T.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2)
          (schurSimpleActionKernel sigma S) (ZMod 2))) ≤ cap o)
    (hhalf : schurSimpleActionKernel sigma S ≠ ⊥ →
      ∀ o : MulAction.orbitRel.Quotient
        (schurSimpleActionKernel sigma S) X,
        2 * cap o ≤ Nat.card o.orbit)
    (hscalar : schurSimpleActionKernel sigma S ≠ ⊥ →
      schurSimpleProductDegree sigma S = 2 →
      ∀ o : MulAction.orbitRel.Quotient
        (schurSimpleActionKernel sigma S) X,
        8 * cap o ≤ 3 * Nat.card o.orbit)
    (hfaithfulClass : schurSimpleActionKernel sigma S = ⊥ →
      schurSimpleProductDegree sigma S = 8 ∨
        9 ≤ schurSimpleProductDegree sigma S)
    (hfaithfulSmallFixed : schurSimpleActionKernel sigma S = ⊥ →
      schurSimpleProductDegree sigma S = 8 →
      5 * Module.finrank (ZMod 2) sigma.invariants ≤ Nat.card X) :
    Non2SchurStructuralBranch sigma S (Nat.card X)
      (Module.finrank (ZMod 2) sigma.invariants) := by
  apply Non2SchurStructuralBranch.of_actionKernel_budgets_of_finrank_le
    sigma S (Nat.card X) (Module.finrank (ZMod 2) sigma.invariants)
    hnonfixed rfl (permutationSection_finrank_le_card sigma M qmap hqmap) ht
  · intro hK
    simpa using (permutationSection_schurMixedSocleDimension_weighted_le
      sigma S hnonfixed M qmap hqmap
      (Module.finrank (ZMod 2) sigma.invariants) rfl
      1 2 cap hcap (by simpa using hhalf hK))
  · intro hK hq
    exact permutationSection_schurMixedSocleDimension_weighted_le
      sigma S hnonfixed M qmap hqmap
      (Module.finrank (ZMod 2) sigma.invariants) rfl
      3 8 cap hcap (hscalar hK hq)
  · exact hfaithfulClass
  · exact hfaithfulSmallFixed

end SymmetricSubgroupAsymptotics

end
