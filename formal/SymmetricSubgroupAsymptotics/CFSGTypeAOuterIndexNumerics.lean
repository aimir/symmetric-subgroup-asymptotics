import SymmetricSubgroupAsymptotics.CFSGTypeAMinimumIndexLower
import SymmetricSubgroupAsymptotics.CFSGTypeALeastIndexSquare
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphismsBounds

/-! A narrow numerical consumer for a future proved actual type-A
outer-cardinality theorem. The structural outer bound remains explicit;
this file does not replace or assert a global literature input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeAOuterIndexNumerics
open PrimitiveSocleRawStructure

 theorem outer_log_of_card_bound (r : ℕ) (hr : 2≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.A r q)]
    (houter : Nat.card (Outer (CFSG.Models.A r q))≤2*(r+1)*Nat.card (q.Field ≃+* q.Field))
    (ell : ℕ) (hell : LeastProperIndex (CFSG.Models.A r q) ell) :
    (Nat.card (Outer (CFSG.Models.A r q)) : ℝ)≤3*Real.logb 2 ell := by
  have hf := CFSGFiniteFieldAutomorphisms.card_ringAut_le_logb q.Field
  rw [q.card_field] at hf
  have hq : 0≤Real.logb 2 q.order := (Nat.cast_nonneg _).trans hf
  have hcoeff : 2*((r : ℝ)+1)≤3*(r : ℝ) := by
    have hrr : (2 : ℝ)≤(r : ℝ) := by exact_mod_cast hr
    linarith
  have hlower := CFSGTypeAMinimumIndexLower.rank_mul_log_order_le_log_leastProperIndex
    r hr q ell hell
  have hout : (Nat.card (Outer (CFSG.Models.A r q)) : ℝ)≤
      (2*((r : ℝ)+1))*(Nat.card (q.Field ≃+* q.Field) : ℝ) := by
    exact_mod_cast houter
  calc
    (Nat.card (Outer (CFSG.Models.A r q)) : ℝ)≤
        (2*((r : ℝ)+1))*(Nat.card (q.Field ≃+* q.Field) : ℝ) := hout
    _≤(2*((r : ℝ)+1))*Real.logb 2 q.order :=
      mul_le_mul_of_nonneg_left hf (by positivity)
    _≤(3*(r : ℝ))*Real.logb 2 q.order := mul_le_mul_of_nonneg_right hcoeff hq
    _=3*((r : ℝ)*Real.logb 2 q.order) := mul_assoc _ _ _
    _≤3*Real.logb 2 ell := mul_le_mul_of_nonneg_left hlower (by norm_num)

 theorem simpleIndexBounds_of_outer_card (r : ℕ) (hr : 2≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.A r q)]
    (houter : Nat.card (Outer (CFSG.Models.A r q))≤2*(r+1)*Nat.card (q.Field ≃+* q.Field))
    (ell : ℕ) (hell : LeastProperIndex (CFSG.Models.A r q) ell) :
    ell^2<Nat.card (CFSG.Models.A r q) ∧
      (Nat.card (Outer (CFSG.Models.A r q)) : ℝ)≤3*Real.logb 2 ell :=
  ⟨CFSGTypeALeastIndexSquare.typeA_leastProperIndex_square_lt_card r hr q ell hell,
    outer_log_of_card_bound r hr q houter ell hell⟩

end SymmetricSubgroupAsymptotics.CFSGTypeAOuterIndexNumerics
