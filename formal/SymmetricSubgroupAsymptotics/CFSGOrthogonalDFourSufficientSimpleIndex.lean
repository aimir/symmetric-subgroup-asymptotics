import SymmetricSubgroupAsymptotics.CFSGSufficientSimpleIndexBounds
import SymmetricSubgroupAsymptotics.CFSGFieldFactorPermutationBudget
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSquare

/-! The actual D4 minimum-index star is enough for the sufficient hybrid.
The only intermediate premises are explicit ACTUAL outer cardinality
bounds,24f in general and6f in characteristic two. They are not assertions
of those unfinished automorphism theorems and are not public T1 inputs.
No stronger minimum-degree or coefficient-three statement is inferred. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure CFSGFiniteFieldAutomorphisms

private theorem odd_small_exponent_one (q : CFSG.PrimePower)
    (hp : 3 ≤ q.prime) {ell : ℕ} (hd : q.order ^ 3 ≤ ell) (hs : ell < 30) :
    q.exponent = 1 := by
  by_contra h
  have he : 2 ≤ q.exponent := by have := q.exponent_pos; omega
  have hn : 9 ≤ q.order := calc
    9 = 3 ^ 2 := by decide
    _ ≤ q.prime ^ 2 := Nat.pow_le_pow_left hp 2
    _ ≤ q.prime ^ q.exponent := pow_le_pow_right₀ (by omega : 1 ≤ q.prime) he
    _ = q.order := rfl
  have h729 : 729 ≤ ell := calc
    729 = 9 ^ 3 := by decide
    _ ≤ q.order ^ 3 := Nat.pow_le_pow_left hn 3
    _ ≤ ell := hd
  omega

theorem typeD_four_sufficientSimpleIndexBudget_of_outer (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.D 4 q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.D 4 q) ell)
    (hOuter : Nat.card (Outer (CFSG.Models.D 4 q)) ≤
      24 * Nat.card (q.Field ≃+* q.Field))
    (hBinary : q.prime = 2 → Nat.card (Outer (CFSG.Models.D 4 q)) ≤
      6 * Nat.card (q.Field ≃+* q.Field)) :
    ell ^ 2 < Nat.card (CFSG.Models.D 4 q) ∧
      SufficientOuterOrderBudget ell (Nat.card (Outer (CFSG.Models.D 4 q))) := by
  have hd : q.order ^ 3 ≤ ell := by
    simpa using typeD_order_power_le_leastProperIndex 4 (by decide) q ell hell
  have ho := typeD_leastProperIndex_square_lt_card 4 q (by decide) ell hell
  refine ⟨ho, ?_⟩
  by_cases hp2 : q.prime = 2
  · have hsharp := typeD_four_six_field_budget q ell hell
    have hb : (Nat.card (Outer (CFSG.Models.D 4 q)) : ℝ) ≤ 3 * Real.logb 2 ell :=
      (by exact_mod_cast hBinary hp2 :
        (Nat.card (Outer (CFSG.Models.D 4 q)) : ℝ) ≤
          6 * (Nat.card (q.Field ≃+* q.Field) : ℝ)).trans hsharp
    have hq2 : 2 ≤ q.order := calc
      2 ≤ q.prime := q.prime_isPrime.two_le
      _ = q.prime ^ 1 := (pow_one _).symm
      _ ≤ q.prime ^ q.exponent := pow_le_pow_right₀
        (by have := q.prime_isPrime.two_le; omega) (by have := q.exponent_pos; omega)
      _ = q.order := rfl
    have he5 : 5 ≤ ell := by
      have hh : 8 ≤ ell := (by simpa using Nat.pow_le_pow_left hq2 3 : 8 ≤ q.order ^ 3).trans hd
      omega
    exact SufficientOuterOrderBudget.of_sharp he5 hb
  · have hp3 : 3 ≤ q.prime := by have := q.prime_isPrime.two_le; omega
    have hq3 : 3 ≤ q.order := calc
      3 ≤ q.prime := hp3
      _ = q.prime ^ 1 := (pow_one _).symm
      _ ≤ q.prime ^ q.exponent := pow_le_pow_right₀ (by omega)
        (by have := q.exponent_pos; omega)
      _ = q.order := rfl
    have he27 : 27 ≤ ell :=
      (by simpa using Nat.pow_le_pow_left hq3 3 : 27 ≤ q.order ^ 3).trans hd
    have h12 := CFSGFieldFactorPermutationBudget.field_factor_le_log_of_power q 12 3 ell hd
      ((by decide : (2 : ℕ) ^ 12 ≤ 3 ^ 9).trans (Nat.pow_le_pow_left hp3 9))
    norm_num at h12
    have houtR : (Nat.card (Outer (CFSG.Models.D 4 q)) : ℝ) ≤
        24 * (Nat.card (q.Field ≃+* q.Field) : ℝ) := by exact_mod_cast hOuter
    refine ⟨by linarith, fun hs => (by omega : False).elim, ?_⟩
    intro hs
    have he := odd_small_exponent_one q hp3 hd hs
    have hf : Nat.card (q.Field ≃+* q.Field) = 1 :=
      (primePower_card_ringAut q).trans he
    simpa only [hf, mul_one] using hOuter

end SymmetricSubgroupAsymptotics.CFSGReduction
