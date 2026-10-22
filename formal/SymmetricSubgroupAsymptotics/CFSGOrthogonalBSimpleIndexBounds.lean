import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOuterCardinality
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexBounds
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBCharTwoSimpleIndex
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphismsBounds

/-! Both simple-index conclusions for the original B family. Odd
characteristic uses the checked actual polar reconstruction and SO index;
characteristic two uses the checked original B-to-C projective equivalence.
No automorphism-recognition or quantitative classical-group input remains. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

theorem typeB_odd_outer_card_le_log (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    (h2 : (2 : q.Field) ≠ 0) [IsSimpleGroup (CFSG.Models.B r q)]
    (ell : ℕ) (hell : LeastProperIndex (CFSG.Models.B r q) ell) :
    (Nat.card (Outer (CFSG.Models.B r q)) : ℝ) ≤ 3 * Real.logb 2 ell := by
  have hqell := typeB_odd_order_le_leastProperIndex r hr q h2 ell hell
  have hq : 0 < q.order := pow_pos q.prime_isPrime.pos _
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast hq : (0 : ℝ) < q.order) (by exact_mod_cast hqell : (q.order : ℝ) ≤ ell)
  have hf := CFSGFiniteFieldAutomorphisms.card_ringAut_le_logb q.Field
  rw [q.card_field] at hf
  have haut0 : (0 : ℝ) ≤ (Nat.card (q.Field ≃+* q.Field) : ℝ) := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ Real.logb 2 ell := haut0.trans (hf.trans hlog)
  calc
    (Nat.card (Outer (CFSG.Models.B r q)) : ℝ) ≤
        2 * (Nat.card (q.Field ≃+* q.Field) : ℝ) := by
      exact_mod_cast typeB_odd_outer_card_le r hr q h2
    _ ≤ 2 * Real.logb 2 ell := mul_le_mul_of_nonneg_left (hf.trans hlog) (by norm_num)
    _ ≤ 3 * Real.logb 2 ell := mul_le_mul_of_nonneg_right (by norm_num) hL0

theorem typeB_odd_simpleIndexBounds (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    (h2 : (2 : q.Field) ≠ 0) [IsSimpleGroup (CFSG.Models.B r q)]
    (ell : ℕ) (hell : LeastProperIndex (CFSG.Models.B r q) ell) :
    ell ^ 2 < Nat.card (CFSG.Models.B r q) ∧
      (Nat.card (Outer (CFSG.Models.B r q)) : ℝ) ≤ 3 * Real.logb 2 ell :=
  ⟨typeB_odd_leastProperIndex_square_lt_card r hr q h2 ell hell,
    typeB_odd_outer_card_le_log r hr q h2 ell hell⟩

theorem typeB_simpleIndexBounds (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.B r q)] : ModelSimpleIndexBounds (.B r q hr) := by
  by_cases hp : q.prime = 2
  · exact typeB_charTwo_simpleIndexBounds r hr q hp
  · have htwo : (2 : q.Field) ≠ 0 := by
      intro h
      have hd : q.prime ∣ 2 := (CharP.cast_eq_zero_iff q.Field q.prime 2).mp h
      exact hp ((Nat.prime_dvd_prime_iff_eq q.prime_isPrime Nat.prime_two).mp hd)
    exact typeB_odd_simpleIndexBounds r hr q htwo

end SymmetricSubgroupAsymptotics.CFSGReduction
