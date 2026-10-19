import SymmetricSubgroupAsymptotics.MarkedC4ProductColumns
import SymmetricSubgroupAsymptotics.MarkedC4VerticalHallBase

/-! The Hall polynomial's entire dependence on the global marking rank
is quadratic. Higher physical columns introduce NO additional r factor. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualSingleGlobalHallPolynomial

def physicalPolynomial (m : ℕ) (A : Type) [CommGroup A] [Finite A] : ℝ :=
  4^m*(∏ k ∈ Finset.range (2+m),((col A k : ℝ)+1))

private theorem two_mark_factors (m r : ℕ) :
    (∏ k ∈ Finset.range (2+m),if k<2 then ((r : ℝ)+1) else 1)=((r : ℝ)+1)^2 := by
  rw [Finset.prod_range_add]
  have ht : (∏ k ∈ Finset.range m,if 2+k<2 then ((r : ℝ)+1) else 1)=1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [if_neg (by omega)]
  rw [ht,mul_one]
  norm_num [Finset.prod_range_succ,pow_two]

/-- P(r)=16(r+1)^2 is paid ONCE. The remaining factor depends only on
the physical abelian group and fixed exponent cutoff. -/
theorem hall_polynomial_le_single_global (m r : ℕ) (A : Type) [CommGroup A] [Finite A] :
    ((∏ k ∈ Finset.range (2+m),
      ((col (A × Multiplicative (Fin r → ZMod 4)) k : ℝ)+1))*4^(2+m))≤
      VerticalHallBase.polynomial r*physicalPolynomial m A := by
  have hfactor (k : ℕ) :
      (col (A × Multiplicative (Fin r → ZMod 4)) k : ℝ)+1≤
        ((col A k : ℝ)+1)*(if k<2 then ((r : ℝ)+1) else 1) := by
    rw [col_prod,col_cyclicFourCoordinates,Nat.cast_add]
    by_cases hk : k<2
    · simp only [if_pos hk]
      have hcr : 0≤(col A k : ℝ)*(r : ℝ) := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      nlinarith
    · simp only [if_neg hk,Nat.cast_zero,add_zero,mul_one]
      exact le_rfl
  have hp :
      (∏ k ∈ Finset.range (2+m),((col (A × Multiplicative (Fin r → ZMod 4)) k : ℝ)+1))≤
        (∏ k ∈ Finset.range (2+m),((col A k : ℝ)+1))*((r : ℝ)+1)^2 := by
    calc
      _≤∏ k ∈ Finset.range (2+m),
          ((col A k : ℝ)+1)*(if k<2 then ((r : ℝ)+1) else 1) := by
        apply Finset.prod_le_prod
        · intro k hk
          positivity
        · intro k hk
          exact hfactor k
      _=_ := by rw [Finset.prod_mul_distrib,two_mark_factors]
  apply (mul_le_mul_of_nonneg_right hp (by positivity : (0 : ℝ)≤4^(2+m))).trans_eq
  unfold VerticalHallBase.polynomial physicalPolynomial
  rw [pow_add]
  norm_num
  ring

end SymmetricSubgroupAsymptotics.MarkedC4.ActualSingleGlobalHallPolynomial
