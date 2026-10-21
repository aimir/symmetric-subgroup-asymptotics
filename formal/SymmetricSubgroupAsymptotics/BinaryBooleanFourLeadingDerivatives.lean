import SymmetricSubgroupAsymptotics.BinaryBooleanFourDifferenceOperators
import SymmetricSubgroupAsymptotics.LeadingOperatorColumns

/-! Difference operators remove a variable from an actual leading
monomial. Only the small order relation on monomial indices is checked
finitely; the conclusion applies to every original vector. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates

open BinaryElementaryPairMonomialWidth

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private theorem removeIndex_strict : ∀ (i : Fin 4) (a j : Fin 16),
    i ∈ support j → j < a → removeIndex i j < removeIndex i a := by decide

private theorem removeIndex_mono (i : Fin 4) {a j : Fin 16} (hj : j ≤ a) :
    removeIndex i j ≤ removeIndex i a := by
  change j.val - 2 ^ i.val ≤ a.val - 2 ^ i.val
  exact Nat.sub_le_sub_right hj _

theorem derivative_hasLeading (i : Fin 4) (a : Fin 16) (v : V)
    (hv : FiniteRowLeadingWeight.HasLeading v a) (hi : i ∈ support a) :
    FiniteRowLeadingWeight.HasLeading (derivative i v) (removeIndex i a) := by
  apply LeadingOperatorColumns.hasLeading_apply_of_columns (derivative i) v a
    (removeIndex i a) hv
  · rw [derivative_basis, if_pos hi]
    simp only [Pi.single_eq_same, ne_eq, one_ne_zero, not_false_eq_true]
  · intro j hj
    rw [derivative_basis]
    by_cases hbit : i ∈ support j
    · rw [if_pos hbit]
      have hne : removeIndex i j ≠ removeIndex i a :=
        ne_of_lt (removeIndex_strict i a j hbit hj)
      simp [Pi.single_apply, hne, Ne.symm hne]
    · rw [if_neg hbit]
      rfl
  · intro c hc j hj
    rw [derivative_basis]
    by_cases hbit : i ∈ support j
    · rw [if_pos hbit]
      have hne : removeIndex i j ≠ c :=
        ne_of_lt (lt_of_le_of_lt (removeIndex_mono i hj) hc)
      simp [Pi.single_apply, hne, Ne.symm hne]
    · rw [if_neg hbit]
      rfl

end SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
