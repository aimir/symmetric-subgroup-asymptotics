import SymmetricSubgroupAsymptotics.BinaryBooleanFourTriangularDifferenceColumns

/-! Every original triangular point permutation lowers a polynomial
with singleton leading term strictly below that same variable. This
holds for every actual group element, not only the tower's selected
bit flips. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
open BinaryElementaryPairMonomialWidth
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private theorem variableIndex_value : ∀ i : Fin 4, (variableIndex i).val = 2 ^ i.val := by decide
private theorem variable_monomial : ∀ (i : Fin 4) (x : Fin 16),
    monomial (support (variableIndex i)) x = bitValue i x := by decide

theorem triangular_low_monomial_difference_prefix
    (p : Equiv.Perm (Fin 16)) (hp : IsTriangularPermutation p)
    (i : Fin 4) (a : Fin 16) (ha : a ≤ variableIndex i) :
    DependsOnPrefix ((fun x => monomial (support a) (p x)) - monomial (support a)) i.val := by
  rcases lt_or_eq_of_le ha with hlt | he
  · let r : Fin 5 := ⟨i.val, by have := i.isLt; omega⟩
    have hsmall : a.val < 2 ^ r.val := by
      change a.val < (variableIndex i).val at hlt
      simpa only [r, variableIndex_value] using hlt
    have hf := monomial_prefix_of_lt a r hsmall
    exact prefix_sub (prefix_comp_triangular hf p hp) hf
  · subst a
    have he : ((fun x => monomial (support (variableIndex i)) (p x)) -
        monomial (support (variableIndex i))) =
        (fun x => bitValue i (p x) - bitValue i x) := by
      funext x
      simp only [Pi.sub_apply, variable_monomial]
    rw [he]
    exact hp i

theorem triangular_singleton_difference_zero_above
    (p : Equiv.Perm (Fin 16)) (hp : IsTriangularPermutation p)
    (i : Fin 4) (v : V)
    (hv : FiniteRowLeadingWeight.HasLeading v (variableIndex i)) :
    ∀ c : Fin 16, variableIndex i ≤ c → permutationDifference p.symm v c = 0 := by
  intro c hc
  rw [LeadingOperatorColumns.apply_eq_sum_columns]
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : a ≤ variableIndex i
  · have hpref := triangular_low_monomial_difference_prefix p hp i a ha
    let r : Fin 5 := ⟨i.val, by have := i.isLt; omega⟩
    have hcv : 2 ^ r.val ≤ c.val := by
      change (variableIndex i).val ≤ c.val at hc
      simpa only [r, variableIndex_value] using hc
    have hz := prefix_polynomial_coefficients_zero _ r hpref c hcv
    have he : permutationDifference p.symm (Pi.single a 1) c = 0 := by
      change evaluate ((fun x => evaluate (Pi.single a 1) (p x))) c -
        (Pi.single a 1 : V) c = 0
      rw [evaluate_basis, ← evaluate_monomial a]
      simpa only [map_sub, Pi.sub_apply] using hz
    rw [he, mul_zero]
  · rw [hv.2 a (lt_of_not_ge ha), zero_mul]

end SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
