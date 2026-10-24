import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Exact natural ceilings of n/sqrt(k), verified through literal
integer-square inequalities. No floating-point estimate, permutation
theorem, or logarithmic approximation is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.IntegerSquareRootQuotientCeiling

theorem ceil_le_of_square (n k c : ℕ) (hk : 0 < k) (hi : n^2 ≤ c^2*k) :
    ⌈(n : ℝ)/Real.sqrt k⌉₊ ≤ c := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hs := Real.sq_sqrt (Nat.cast_nonneg k)
  have hiR : (n : ℝ)^2 ≤ (c : ℝ)^2*(k : ℝ) := by exact_mod_cast hi
  have hh : (n : ℝ) ≤ (c : ℝ)*Real.sqrt k := by
    apply (sq_le_sq₀ (Nat.cast_nonneg n) (by positivity)).mp
    rw [mul_pow, hs]
    exact hiR
  exact Nat.ceil_le.mpr ((div_le_iff₀ (Real.sqrt_pos.mpr hkR)).mpr hh)

theorem le_ceil_of_square (n k c : ℕ) (hk : 0 < k) (hc : 0 < c)
    (lo : (c-1)^2*k < n^2) : c ≤ ⌈(n : ℝ)/Real.sqrt k⌉₊ := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hs := Real.sq_sqrt (Nat.cast_nonneg k)
  have hlo : ((c-1 : ℕ) : ℝ)^2*(k : ℝ) < (n : ℝ)^2 := by exact_mod_cast lo
  have hh : ((c-1 : ℕ) : ℝ)*Real.sqrt k < (n : ℝ) := by
    apply (sq_lt_sq₀ (by positivity) (Nat.cast_nonneg n)).mp
    rw [mul_pow, hs]
    exact hlo
  have hlt : c-1 < ⌈(n : ℝ)/Real.sqrt k⌉₊ :=
    Nat.lt_ceil.mpr ((lt_div_iff₀ (Real.sqrt_pos.mpr hkR)).mpr hh)
  omega

theorem ceil_eq_of_square_interval (n k c : ℕ) (hk : 0 < k) (hc : 0 < c)
    (lo : (c-1)^2*k < n^2) (hi : n^2 ≤ c^2*k) :
    ⌈(n : ℝ)/Real.sqrt k⌉₊ = c :=
  Nat.le_antisymm (ceil_le_of_square n k c hk hi) (le_ceil_of_square n k c hk hc lo)

end SymmetricSubgroupAsymptotics.IntegerSquareRootQuotientCeiling
