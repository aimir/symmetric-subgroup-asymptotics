import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-! Abstract canonical group charts for every actual order-four block image.
Together with the actual regular orbit chart this supplies its equivariant
C4 or V4 coordinates, independently of its permutation labels. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CardFourCyclicOrKleinChart
variable {Q C K : Type} [Group Q] [Group C] [Group K]

theorem cyclic_or_klein (hQ : Nat.card Q=4) : IsCyclic Q ∨ IsKleinFour Q := by
  classical
  by_cases h : IsCyclic Q
  · exact Or.inl h
  · exact Or.inr ⟨hQ,
      (not_isCyclic_iff_exponent_eq_prime (α := Q) Nat.prime_two
        (by simpa using hQ)).mp h⟩

/-- Only the two canonical target groups, not a source capacity, are supplied. -/
theorem canonical_chart [IsCyclic C] [IsKleinFour K]
    (hC : Nat.card C=4) (hQ : Nat.card Q=4) :
    Nonempty (Q ≃* C) ∨ Nonempty (Q ≃* K) := by
  rcases cyclic_or_klein hQ with h | h
  · letI := h
    exact Or.inl ⟨mulEquivOfCyclicCardEq (hQ.trans hC.symm)⟩
  · letI := h
    exact Or.inr IsKleinFour.nonempty_mulEquiv
end SymmetricSubgroupAsymptotics.CardFourCyclicOrKleinChart
