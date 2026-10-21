import SymmetricSubgroupAsymptotics.BinaryBooleanFourPrefixFunctions
import SymmetricSubgroupAsymptotics.BinaryBooleanFourLeadingProducts
import SymmetricSubgroupAsymptotics.BinaryBooleanFourTriangularLeading

/-! Multiplying a lower-block error by a new highest variable shifts its
support by exactly that variable. These are pointwise Boolean products,
with all arbitrary original lower coefficients retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
open BinaryElementaryPairMonomialWidth
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private theorem variable_union_low_value : ∀ (j : Fin 4) (a : Fin 16),
    a.val < 2 ^ j.val → (unionIndex (variableIndex j) a).val = 2 ^ j.val + a.val := by decide

private theorem higherBlock_union_variable : ∀ (i j : Fin 4) (a : Fin 16),
    i < j → a.val < 2 ^ j.val →
      higherBlock i (unionIndex (variableIndex j) a) = 2 ^ j.val + higherBlock i a := by decide

theorem monomialVariable_shift_error (j : Fin 4) (r : ℕ) (hr : r ≤ 2 ^ j.val)
    (v : V) (hv : ∀ a : Fin 16, r ≤ a.val → v a = 0) :
    ∀ c : Fin 16, 2 ^ j.val + r ≤ c.val → monomialMultiplier (variableIndex j) v c = 0 := by
  intro c hc
  rw [LeadingOperatorColumns.apply_eq_sum_columns]
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : a.val < r
  · rw [monomialMultiplier_basis]
    have hval := variable_union_low_value j a (lt_of_lt_of_le ha hr)
    have hne : unionIndex (variableIndex j) a ≠ c := by
      intro he
      have he' := congrArg Fin.val he
      omega
    simp only [Pi.single_apply, if_neg (Ne.symm hne), mul_zero]
  · rw [hv a (le_of_not_gt ha), zero_mul]

theorem monomialVariable_shift_higherBlock_error
    (i j : Fin 4) (a : Fin 16) (hij : i < j) (ha : a.val < 2 ^ j.val)
    (v : V) (hv : ∀ b : Fin 16, higherBlock i a ≤ b.val → v b = 0) :
    ∀ c : Fin 16, higherBlock i (unionIndex (variableIndex j) a) ≤ c.val →
      monomialMultiplier (variableIndex j) v c = 0 := by
  have hr : higherBlock i a ≤ 2 ^ j.val := by
    have hdiv := Nat.div_mul_le_self a.val (2 ^ (i.val + 1))
    change a.val / 2 ^ (i.val + 1) * 2 ^ (i.val + 1) ≤ 2 ^ j.val
    omega
  intro c hc
  rw [higherBlock_union_variable i j a hij ha] at hc
  exact monomialVariable_shift_error j _ hr v hv c hc

end SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
