import SymmetricSubgroupAsymptotics.BinaryPairPolynomialCoordinates

/-! Leading pointwise products of arbitrary polynomial functions.
Lower terms of the actual kernel vector are retained. Disjoint leading
supports make the leading union unique, using union ≤ integer addition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates

open BinaryElementaryPairMonomialWidth
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def polynomialMultiply (f : V) : V →ₗ[ZMod 2] V :=
  evaluate.comp ((multiplyFunction (evaluate f)).comp evaluate)

private theorem unionIndex_le_add : ∀ a b : Fin 16,
    (unionIndex a b).val ≤ a.val + b.val := by decide

private theorem unionIndex_eq_add : ∀ a b : Fin 16,
    Disjoint (support a) (support b) → (unionIndex a b).val = a.val + b.val := by decide

theorem polynomialMultiply_basis (f : V) (a : Fin 16) :
    polynomialMultiply f (Pi.single a 1) = monomialMultiplier a f := by
  change evaluate (evaluate f * evaluate (Pi.single a 1)) =
    evaluate (monomial (support a) * evaluate f)
  rw [evaluate_basis, mul_comm]

private theorem polynomialMultiply_column (f : V) (a c : Fin 16) :
    polynomialMultiply f (Pi.single a 1) c =
      ∑ i : Fin 16, f i * (Pi.single (unionIndex a i) 1 : V) c := by
  rw [polynomialMultiply_basis, LeadingOperatorColumns.apply_eq_sum_columns]
  simp only [monomialMultiplier_basis]

theorem polynomialMultiply_hasLeading (f v : V) (b a : Fin 16)
    (hf : FiniteRowLeadingWeight.HasLeading f b)
    (hv : FiniteRowLeadingWeight.HasLeading v a)
    (hdisj : Disjoint (support a) (support b)) :
    FiniteRowLeadingWeight.HasLeading (polynomialMultiply f v) (unionIndex a b) := by
  have hsum : (unionIndex a b).val = a.val + b.val := unionIndex_eq_add a b hdisj
  have hdiag : polynomialMultiply f (Pi.single a 1) (unionIndex a b) = f b := by
    rw [polynomialMultiply_column]
    calc
      (∑ i : Fin 16, f i * (Pi.single (unionIndex a i) 1 : V) (unionIndex a b)) =
          f b * (Pi.single (unionIndex a b) 1 : V) (unionIndex a b) := by
        apply Finset.sum_eq_single b
        · intro i _ hib
          rcases lt_or_gt_of_ne hib with hi | hi
          · have hbound := unionIndex_le_add a i
            have hne : unionIndex a i ≠ unionIndex a b := by
              intro he
              have he' := congrArg Fin.val he
              omega
            simp [Pi.single_apply, hne, Ne.symm hne]
          · rw [hf.2 i hi, zero_mul]
        · intro hb
          exact False.elim (hb (Finset.mem_univ b))
      _ = f b := by simp only [Pi.single_eq_same, mul_one]
  apply LeadingOperatorColumns.hasLeading_apply_of_columns (polynomialMultiply f) v a
    (unionIndex a b) hv
  · rw [hdiag]
    exact hf.1
  · intro j hj
    rw [polynomialMultiply_column]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i ≤ b
    · have hbound := unionIndex_le_add j i
      have hne : unionIndex j i ≠ unionIndex a b := by
        intro he
        have he' := congrArg Fin.val he
        omega
      simp [Pi.single_apply, hne, Ne.symm hne]
    · rw [hf.2 i (lt_of_not_ge hi), zero_mul]
  · intro c hc j hj
    rw [polynomialMultiply_column]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i ≤ b
    · have hbound := unionIndex_le_add j i
      have hne : unionIndex j i ≠ c := by
        intro he
        have he' := congrArg Fin.val he
        change (unionIndex a b).val < c.val at hc
        omega
      simp [Pi.single_apply, hne, Ne.symm hne]
    · rw [hf.2 i (lt_of_not_ge hi), zero_mul]

end SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
