import SymmetricSubgroupAsymptotics.BinaryBooleanFourKernelLeadingClosure
import SymmetricSubgroupAsymptotics.LeadingOperatorColumns

/-! Four actual polynomial vectors with singleton leading terms separate
the same sixteen Boolean points. Their arbitrary lower coefficients are
retained; no vector is replaced by its leading monomial. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
open BinaryElementaryPairMonomialWidth
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private theorem first_distinct_variable : ∀ x y : Fin 16, x ≠ y →
    ∃ i : Fin 4,
      monomial (support (variableIndex i)) x ≠ monomial (support (variableIndex i)) y ∧
      ∀ a : Fin 16, a < variableIndex i → monomial (support a) x = monomial (support a) y := by decide

private theorem evaluate_difference_columns (v : V) (x y : Fin 16) :
    evaluate v x - evaluate v y =
      ∑ a : Fin 16, v a * (monomial (support a) x - monomial (support a) y) := by
  rw [LeadingOperatorColumns.apply_eq_sum_columns, LeadingOperatorColumns.apply_eq_sum_columns]
  simp_rw [evaluate_basis, mul_sub]
  rw [Finset.sum_sub_distrib]

theorem singleton_leading_point_family_injective (v : Fin 4 → V)
    (hlead : ∀ i, FiniteRowLeadingWeight.HasLeading (v i) (variableIndex i)) :
    Function.Injective (fun x : Fin 16 => fun i : Fin 4 => evaluate (v i) x) := by
  intro x y he
  by_contra hne
  obtain ⟨i, hi, hsmall⟩ := first_distinct_variable x y hne
  have hd : evaluate (v i) x - evaluate (v i) y =
      v i (variableIndex i) *
        (monomial (support (variableIndex i)) x - monomial (support (variableIndex i)) y) := by
    rw [evaluate_difference_columns]
    apply Finset.sum_eq_single (variableIndex i)
    · intro a _ hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [hsmall a hlt, sub_self, mul_zero]
      · rw [(hlead i).2 a hgt, zero_mul]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  have hn : evaluate (v i) x - evaluate (v i) y ≠ 0 := by
    rw [hd]
    exact mul_ne_zero (hlead i).1 (sub_ne_zero.mpr hi)
  exact hn (sub_eq_zero.mpr (congrFun he i))

end SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
