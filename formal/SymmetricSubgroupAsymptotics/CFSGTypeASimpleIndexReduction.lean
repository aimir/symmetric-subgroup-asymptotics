import SymmetricSubgroupAsymptotics.CFSGPSLTwoSimpleIndexReduction
import SymmetricSubgroupAsymptotics.CFSGTypeAOuterCardinality
import SymmetricSubgroupAsymptotics.CFSGTypeAOuterIndexNumerics

/-! The entire original type-A family is discharged from the concrete
simple-index residual. Higher rank uses the actual root geometry and
coordinate reconstruction; rank one keeps the separately proved
square-scalar bound, including its original small-field guard. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

theorem typeA_highRank_simpleIndexBounds (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    [hSimple : IsSimpleGroup (CFSG.Models.A r q)] :
    ∀ ell : ℕ, LeastProperIndex (CFSG.Models.A r q) ell →
      ell ^ 2 < Nat.card (CFSG.Models.A r q) ∧
        (Nat.card (Outer (CFSG.Models.A r q)) : ℝ) ≤ 3 * Real.logb 2 ell := by
  have hout : Nat.card (Outer (CFSG.Models.A r q)) ≤
      2 * (r + 1) * Nat.card (q.Field ≃+* q.Field) := by
    letI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin (r + 1)) q.Field) := hSimple
    exact CFSGTypeAOuterCardinality.outer_card_le q.prime (by omega)
  exact CFSGTypeAOuterIndexNumerics.simpleIndexBounds_of_outer_card r hr q hout

theorem typeA_simpleIndexBounds (r : ℕ) (q : CFSG.PrimePower)
    (hr : 1 ≤ r) (hs : r = 1 → 4 ≤ q.order)
    [IsSimpleGroup (CFSG.Models.A r q)] :
    ∀ ell : ℕ, LeastProperIndex (CFSG.Models.A r q) ell →
      ell ^ 2 < Nat.card (CFSG.Models.A r q) ∧
        (Nat.card (Outer (CFSG.Models.A r q)) : ℝ) ≤ 3 * Real.logb 2 ell := by
  by_cases he : r = 1
  · subst r
    exact typeA_rank_one_simpleIndexBounds q (hs rfl)
  · exact typeA_highRank_simpleIndexBounds r (by omega) q

def RemainingSimpleIndexModelWithoutTypeASuzuki : CFSG.Index → Prop
  | .A _ _ _ _ => False
  | i => RemainingSimpleIndexModelWithoutSuzukiPSLTwo i

theorem simpleIndex_model_or_remaining_without_typeA_suzuki (i : CFSG.Index)
    [IsSimpleGroup i.Model] (hn : ¬ IsMulCommutative i.Model) :
    ModelSimpleIndexBounds i ∨ RemainingSimpleIndexModelWithoutTypeASuzuki i := by
  cases i <;> try exact simpleIndex_model_or_remaining_without_suzuki_pslTwo _ hn
  case A r q hr hs hsimple =>
    letI : IsSimpleGroup (CFSG.Models.A r q) := hsimple
    exact Or.inl (typeA_simpleIndexBounds r q (by omega) hs)

theorem publishedSimpleIndexBounds_of_cfsg_and_remaining_non_typeA_suzuki_models
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingSimpleIndexModelWithoutTypeASuzuki i →
        ModelSimpleIndexBounds i) : PublishedSimpleIndexBounds := by
  apply publishedSimpleIndexBounds_of_cfsg_and_remaining_non_suzuki_pslTwo_models hCFSG
  intro i _ _ hn hi
  cases i <;> try exact remaining _ hn hi
  case A r q hr hs hfinite hsimple =>
    letI : IsSimpleGroup (CFSG.Models.A r q) := hsimple
    exact typeA_simpleIndexBounds r q (by omega) hs

end SymmetricSubgroupAsymptotics.CFSGReduction
