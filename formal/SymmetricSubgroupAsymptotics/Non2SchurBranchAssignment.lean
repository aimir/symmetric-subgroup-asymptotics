import SymmetricSubgroupAsymptotics.Non2SchurActionKernel
import SymmetricSubgroupAsymptotics.Non2SchurRowCertificates

/-!
# Assigning an actual Schur row to the four capacity branches

This file separates the remaining group and permutation facts from all
Schur and numerical bookkeeping.  Once the literal action kernel has the
normal-orbit bounds below, and a faithful row satisfies the small/large
image alternative, the actual row enters one of the four checked capacity
certificates automatically.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

variable {B A : Type} [Group B]
    [AddCommGroup A] [Module (ZMod 2) A]

/-- Exact structural assembly for one actual nonfixed row.  The hypotheses
left here are the permutation-theoretic normal-orbit bounds and the
faithful-image `8`-or-`>=9` alternative; every other part of the row
assignment is proved. -/
theorem Non2SchurStructuralBranch.of_actionKernel_budgets
    [FiniteDimensional (ZMod 2) A]
    (sigma : Representation (ZMod 2) B A)
    (S : Submodule (ZMod 2)[B] sigma.asModule)
    [IsSimpleModule (ZMod 2)[B] S]
    (s t : Nat)
    (hnonfixed : ¬ representationSubmoduleFixed sigma S)
    (ht : 32 * t ≤ 11 * s)
    (hphysical : schurMixedSocleDimension sigma S t ≤ s)
    (hnonfaithfulHalf : schurSimpleActionKernel sigma S ≠ ⊥ →
      2 * schurMixedSocleDimension sigma S t ≤ s)
    (hscalar : schurSimpleActionKernel sigma S ≠ ⊥ →
      schurSimpleProductDegree sigma S = 2 →
      8 * schurMixedSocleDimension sigma S t ≤ 3 * s)
    (hfaithfulClass : schurSimpleActionKernel sigma S = ⊥ →
      schurSimpleProductDegree sigma S = 8 ∨
        9 ≤ schurSimpleProductDegree sigma S)
    (hfaithfulSmallFixed : schurSimpleActionKernel sigma S = ⊥ →
      schurSimpleProductDegree sigma S = 8 → 5 * t ≤ s) :
    Non2SchurStructuralBranch sigma S s t := by
  classical
  let L := schurMixedSocleDimension sigma S t
  let q := schurSimpleProductDegree sigma S
  have hq2 : 2 ≤ q := by
    exact two_le_schurSimpleProductDegree_of_nonfixed sigma S hnonfixed
  change (32 * t ≤ 11 * s ∧ 2 * L ≤ s ∧ 3 ≤ q) ∨
    (8 * L ≤ 3 * s ∧ q = 2) ∨
    (5 * t ≤ s ∧ L ≤ s ∧ q = 8) ∨
    (32 * t ≤ 11 * s ∧ L ≤ s ∧ 9 ≤ q)
  by_cases hK : schurSimpleActionKernel sigma S = ⊥
  · rcases hfaithfulClass hK with hq8 | hq9
    · exact Or.inr (Or.inr (Or.inl
        ⟨hfaithfulSmallFixed hK hq8, hphysical, hq8⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ht, hphysical, hq9⟩))
  · by_cases hq : q = 2
    · exact Or.inr (Or.inl ⟨hscalar hK hq, hq⟩)
    · left
      exact ⟨ht, hnonfaithfulHalf hK, by omega⟩

end SymmetricSubgroupAsymptotics

end
