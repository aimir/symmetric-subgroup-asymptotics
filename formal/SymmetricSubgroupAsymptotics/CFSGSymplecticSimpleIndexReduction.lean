import SymmetricSubgroupAsymptotics.CFSGSymplecticOuterCardinality
import SymmetricSubgroupAsymptotics.CFSGSymplecticLeastIndexSquare
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphismsBounds
import SymmetricSubgroupAsymptotics.CFSGTypeASimpleIndexReduction

/-! The entire original C family now satisfies both required simple
index inequalities. The actual Out bound is proved above; no outer
recognition or quantitative classical-group theorem is a premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

theorem typeC_simpleIndexBounds (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (hs : r = 2 → q.order ≠ 2) [IsSimpleGroup (CFSG.Models.C r q)]
    (ell : ℕ) (hell : LeastProperIndex (CFSG.Models.C r q) ell) :
    ell ^ 2 < Nat.card (CFSG.Models.C r q) ∧
      (Nat.card (Outer (CFSG.Models.C r q)) : ℝ) ≤ 3 * Real.logb 2 ell := by
  refine ⟨typeC_leastProperIndex_square_lt_card r q hr hs ell hell, ?_⟩
  have hqell := typeC_order_le_leastProperIndex r hr q ell hell
  have hq : 0 < q.order := pow_pos q.prime_isPrime.pos _
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast hq : (0 : ℝ) < q.order) (by exact_mod_cast hqell : (q.order : ℝ) ≤ ell)
  have hf := CFSGFiniteFieldAutomorphisms.card_ringAut_le_logb q.Field
  rw [q.card_field] at hf
  have hout : (Nat.card (Outer (CFSG.Models.C r q)) : ℝ) ≤
      3 * (Nat.card (q.Field ≃+* q.Field) : ℝ) := by
    exact_mod_cast typeC_outer_card_le r hr q
  exact hout.trans ((mul_le_mul_of_nonneg_left hf (by norm_num)).trans
    (mul_le_mul_of_nonneg_left hlog (by norm_num)))

def RemainingSimpleIndexModelWithoutTypeASuzukiC : CFSG.Index → Prop
  | .C _ _ _ _ => False
  | i => RemainingSimpleIndexModelWithoutTypeASuzuki i

theorem simpleIndex_model_or_remaining_without_typeA_suzuki_C (i : CFSG.Index)
    [IsSimpleGroup i.Model] (hn : ¬ IsMulCommutative i.Model) :
    ModelSimpleIndexBounds i ∨ RemainingSimpleIndexModelWithoutTypeASuzukiC i := by
  cases i <;> try exact simpleIndex_model_or_remaining_without_typeA_suzuki _ hn
  case C r q hr hs hsimple =>
    letI : IsSimpleGroup (CFSG.Models.C r q) := hsimple
    exact Or.inl (typeC_simpleIndexBounds r hr q hs)

theorem publishedSimpleIndexBounds_of_cfsg_and_remaining_non_typeA_suzuki_C_models
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingSimpleIndexModelWithoutTypeASuzukiC i →
        ModelSimpleIndexBounds i) : PublishedSimpleIndexBounds := by
  apply publishedSimpleIndexBounds_of_cfsg_and_remaining_non_typeA_suzuki_models hCFSG
  intro i _ _ hn _
  rcases simpleIndex_model_or_remaining_without_typeA_suzuki_C i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
