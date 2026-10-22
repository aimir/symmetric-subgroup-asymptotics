import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOuterCardinality
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexStarLower
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSquare
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphismsBounds

/-! Both required simple-index conclusions for EVERY original type-D
model of rank at least five, in every characteristic. The proved actual
polar realization and O/E index give the field factor; the original
root-star lower bound supplies the logarithmic budget. Rank four remains
the separate genuine triality case. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

theorem typeD_high_outer_card_le_log (r : ℕ) (hr : 5≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.D r q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.D r q) ell) :
    (Nat.card (Outer (CFSG.Models.D r q)) : ℝ)≤3*Real.logb 2 ell := by
  have hpow := typeD_order_power_le_leastProperIndex r (by omega) q ell hell
  have hq : 0<q.order := pow_pos q.prime_isPrime.pos _
  have hpowR : (q.order : ℝ)^(r-1)≤(ell : ℝ) := by exact_mod_cast hpow
  have hl := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (by positivity : (0:ℝ)<(q.order:ℝ)^(r-1)) hpowR
  rw [Real.logb_pow] at hl
  have hf := CFSGFiniteFieldAutomorphisms.card_ringAut_le_logb q.Field
  rw [q.card_field] at hf
  have hL0 : (0:ℝ)≤Real.logb 2 q.order := (Nat.cast_nonneg _).trans hf
  have hcoef : (8:ℝ)≤3*(r-1:ℕ) := by
    exact_mod_cast (show 8≤3*(r-1) by omega)
  calc
    (Nat.card (Outer (CFSG.Models.D r q)) : ℝ)≤
        8*(Nat.card (q.Field≃+*q.Field) : ℝ) := by
      exact_mod_cast typeD_high_outer_card_le r hr q
    _ ≤8*Real.logb 2 q.order := mul_le_mul_of_nonneg_left hf (by norm_num)
    _ ≤(3*(r-1:ℕ))*Real.logb 2 q.order := mul_le_mul_of_nonneg_right hcoef hL0
    _ =3*((r-1:ℕ)*Real.logb 2 q.order) := by ring
    _ ≤3*Real.logb 2 ell := mul_le_mul_of_nonneg_left hl (by norm_num)

theorem typeD_high_simpleIndexBounds (r : ℕ) (hr : 5≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.D r q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.D r q) ell) :
    ell^2<Nat.card (CFSG.Models.D r q) ∧
      (Nat.card (Outer (CFSG.Models.D r q)) : ℝ)≤3*Real.logb 2 ell :=
  ⟨typeD_leastProperIndex_square_lt_card r q (by omega) ell hell,
    typeD_high_outer_card_le_log r hr q ell hell⟩

end SymmetricSubgroupAsymptotics.CFSGReduction
