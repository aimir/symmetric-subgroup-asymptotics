import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! A fraction-free finite-field zero-count consequence of mathlib's
proved Schwartz--Zippel theorem. This is an elementary shared counting
tool; neither classification nor an external polynomial estimate is used. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGPolynomialZeroCardinality

theorem polynomial_zero_card_le {K : Type*} [Field K] [Finite K] (n D : ℕ)
    (p : MvPolynomial (Fin (n + 1)) K) (hp : p ≠ 0) (hD : p.totalDegree ≤ D) :
    Nat.card {v : Fin (n + 1) → K // MvPolynomial.eval v p = 0} ≤ D * Nat.card K ^ n := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  have h := MvPolynomial.schwartz_zippel_totalDegree hp (Finset.univ : Finset K)
  have hbase :
      (Nat.card {v : Fin (n + 1) → K // MvPolynomial.eval v p = 0} : ℚ≥0) /
        (Nat.card K : ℚ≥0) ^ (n + 1) ≤ (p.totalDegree : ℚ≥0) / (Nat.card K : ℚ≥0) := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using h
  have hratio := hbase.trans (div_le_div_of_nonneg_right
    (by exact_mod_cast hD : (p.totalDegree : ℚ≥0) ≤ D) (by positivity))
  have hq : (0 : ℚ≥0) < Nat.card K := by exact_mod_cast Nat.card_pos (α := K)
  have hm := (div_le_div_iff₀ (pow_pos hq _) hq).mp hratio
  rw [pow_succ, ← mul_assoc] at hm
  have hbound := (mul_le_mul_iff_left₀ hq).mp hm
  exact_mod_cast hbound

end SymmetricSubgroupAsymptotics.CFSGPolynomialZeroCardinality
