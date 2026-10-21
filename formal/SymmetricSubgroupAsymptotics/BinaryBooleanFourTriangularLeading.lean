import SymmetricSubgroupAsymptotics.BinaryBooleanFourLeadingDerivatives

/-! Boolean derivatives remain valid leading operators in the presence
of arbitrary triangular errors. No pure translation is required: each
column error may occupy every monomial below its higher-bit block. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
open BinaryElementaryPairMonomialWidth
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def higherBlock (i : Fin 4) (a : Fin 16) : ℕ :=
  a.val / 2 ^ (i.val + 1) * 2 ^ (i.val + 1)

private theorem higherBlock_le_removed : ∀ (i : Fin 4) (a j : Fin 16),
    i ∈ support a → j ≤ a → higherBlock i j ≤ (removeIndex i a).val := by decide

theorem triangular_derivative_hasLeading
    (T : V →ₗ[ZMod 2] V) (i : Fin 4)
    (hcolumns : ∀ (a c : Fin 16), higherBlock i a ≤ c.val →
      T (Pi.single a 1) c = derivative i (Pi.single a 1) c)
    (v : V) (a : Fin 16) (hv : FiniteRowLeadingWeight.HasLeading v a)
    (hi : i ∈ support a) :
    FiniteRowLeadingWeight.HasLeading (T v) (removeIndex i a) := by
  have he (c : Fin 16) (hc : removeIndex i a ≤ c) : T v c = derivative i v c := by
    rw [LeadingOperatorColumns.apply_eq_sum_columns,
      LeadingOperatorColumns.apply_eq_sum_columns]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ≤ a
    · rw [hcolumns j c ((higherBlock_le_removed i a j hi hj).trans hc)]
    · rw [hv.2 j (lt_of_not_ge hj), zero_mul, zero_mul]
  have hd := derivative_hasLeading i a v hv hi
  refine ⟨?_, ?_⟩
  · rw [he _ le_rfl]
    exact hd.1
  · intro c hc
    rw [he c (le_of_lt hc)]
    exact hd.2 c hc

end SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
