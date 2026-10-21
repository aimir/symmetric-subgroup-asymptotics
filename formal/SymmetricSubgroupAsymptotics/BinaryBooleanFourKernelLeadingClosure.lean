import SymmetricSubgroupAsymptotics.BinaryBooleanFourLargeQuadraticSet

/-! Actual difference-stable kernel vectors with five quadratic leading
supports provide every linear leading support and the constant support.
All lower terms remain in the same original scalar subspace. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates

open BinaryElementaryPairMonomialWidth
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def variableIndex (i : Fin 4) : Fin 16 := ![1, 2, 4, 8] i

private theorem remove_quadratic_to_variable : ∀ (a : Fin 16) (i : Fin 4),
    (support a).card = 2 → i ∈ support a →
      ∃ j : Fin 4, j ∈ support a ∧ removeIndex j a = variableIndex i := by decide

private theorem variable_remove : ∀ i : Fin 4,
    i ∈ support (variableIndex i) ∧ removeIndex i (variableIndex i) = 0 := by decide

private theorem small_support_index : ∀ a : Fin 16,
    (support a).card ≤ 1 → a = 0 ∨ ∃ i : Fin 4, a = variableIndex i := by decide

theorem five_quadratic_leading_vectors_give_small_supports
    (K : Submodule (ZMod 2) V)
    (hstable : ∀ i : Fin 4, ∀ f ∈ K, derivative i f ∈ K)
    (Q : Finset (Fin 16))
    (hQ : ∀ a ∈ Q, (support a).card = 2) (hcard : 5 ≤ Q.card)
    (hactual : ∀ a ∈ Q, ∃ f ∈ K, FiniteRowLeadingWeight.HasLeading f a) :
    ∀ a : Fin 16, (support a).card ≤ 1 →
      ∃ f ∈ K, FiniteRowLeadingWeight.HasLeading f a := by
  have hlinear (i : Fin 4) :
      ∃ f ∈ K, FiniteRowLeadingWeight.HasLeading f (variableIndex i) := by
    obtain ⟨a, ha, hi⟩ := every_variable_covered_by_five_quadratics Q hQ hcard i
    obtain ⟨f, hf, hlead⟩ := hactual a ha
    obtain ⟨j, hj, he⟩ := remove_quadratic_to_variable a i (hQ a ha) hi
    refine ⟨derivative j f, hstable j f hf, ?_⟩
    rw [← he]
    exact derivative_hasLeading j a f hlead hj
  have hconstant : ∃ f ∈ K, FiniteRowLeadingWeight.HasLeading f 0 := by
    obtain ⟨f, hf, hlead⟩ := hlinear 0
    refine ⟨derivative 0 f, hstable 0 f hf, ?_⟩
    have h := derivative_hasLeading 0 (variableIndex 0) f hlead (variable_remove 0).1
    simpa only [(variable_remove 0).2] using h
  intro a ha
  rcases small_support_index a ha with rfl | ⟨i, rfl⟩
  · exact hconstant
  · exact hlinear i

end SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
