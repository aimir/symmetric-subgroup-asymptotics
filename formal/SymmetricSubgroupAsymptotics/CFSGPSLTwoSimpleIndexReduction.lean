import SymmetricSubgroupAsymptotics.CFSGSuzukiSimpleIndexReduction
import SymmetricSubgroupAsymptotics.CFSGPSLTwoIndexNumerics

/-! Exact simple-index dispatch for the pinned rank-one type-A model.
The model is the original projective special linear group over q.Field;
the original small-field guard supplies its cardinality-at-least-four
hypothesis. Higher-rank type A remains an explicit open obligation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

theorem typeA_rank_one_simpleIndexBounds (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.A 1 q)] (hq : 4≤q.order) :
    ∀ ell : ℕ, LeastProperIndex (CFSG.Models.A 1 q) ell →
      ell^2<Nat.card (CFSG.Models.A 1 q) ∧
        (Nat.card (Outer (CFSG.Models.A 1 q)) : ℝ)≤3*Real.logb 2 ell := by
  have hfield : 4≤Nat.card q.Field := by simpa only [q.card_field] using hq
  exact CFSGPSLTwoGeometry.simpleIndexBounds hfield

/-- The existing residual predicate with precisely the now-proved A1
branch removed. Its higher-rank type-A cases are retained. -/
def RemainingSimpleIndexModelWithoutSuzukiPSLTwo : CFSG.Index→Prop
  | .A r _ _ _ => r≠1
  | i => RemainingSimpleIndexModelWithoutSuzuki i

theorem simpleIndex_model_or_remaining_without_suzuki_pslTwo (i : CFSG.Index)
    [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model) :
    ModelSimpleIndexBounds i∨RemainingSimpleIndexModelWithoutSuzukiPSLTwo i := by
  cases i <;> try exact simpleIndex_model_or_remaining_without_suzuki _ hn
  case A r q hr hs hsimple =>
    by_cases he : r=1
    · subst r
      letI : IsSimpleGroup (CFSG.Models.A 1 q) := hsimple
      exact Or.inl (typeA_rank_one_simpleIndexBounds q (hs rfl))
    · exact Or.inr he

theorem publishedSimpleIndexBounds_of_cfsg_and_remaining_non_suzuki_pslTwo_models
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model→RemainingSimpleIndexModelWithoutSuzukiPSLTwo i→
        ModelSimpleIndexBounds i) : PublishedSimpleIndexBounds := by
  apply publishedSimpleIndexBounds_of_cfsg_and_remaining_non_suzuki_models hCFSG
  intro i _ _ hn hi
  cases i <;> try exact remaining _ hn hi
  case A r q hr hs hfinite hsimple =>
    by_cases he : r=1
    · subst r
      letI : IsSimpleGroup (CFSG.Models.A 1 q) := hsimple
      exact typeA_rank_one_simpleIndexBounds q (hs rfl)
    · exact remaining (.A r q hr hs) hn he

end SymmetricSubgroupAsymptotics.CFSGReduction
