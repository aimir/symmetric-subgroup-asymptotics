import SymmetricSubgroupAsymptotics.CFSGTypeAFiniteFieldGeneration
import SymmetricSubgroupAsymptotics.CFSGSimpleGenerationReduction

/-! Exact dispatch of the proved literal matrix type-A family. The
pinned model is definitionally PSL_(r+1)(q.Field); its original rank and
small-field guards are retained. The residual callback below removes
precisely type A from the existing concrete generation obligations. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGGeneration

theorem typeA_twoGenerated (r : ℕ) (q : CFSG.PrimePower) (hr : 1≤r)
    (hsmall : r=1→4≤q.order) : TwoGenerated (CFSG.Models.A r q) := by
  have hg : r+1=2→4≤Nat.card q.Field := by
    intro he
    rw [q.card_field]
    exact hsmall (by omega)
  obtain ⟨x,y,hxy⟩ := CFSGTypeAFiniteFieldGeneration.psl_exists_generating_pair
    (F:=q.Field) (r+1) (by omega) hg
  refine ⟨{x,y},?_,Finset.card_le_two⟩
  simpa only [Finset.coe_insert,Finset.coe_singleton] using hxy

/-- Exactly the old residual model predicate with its now-proved type-A
branch removed. No other remaining model obligation is weakened. -/
def RemainingGenerationIndexWithoutTypeA : CFSG.Index→Prop
  | .A _ _ _ _ => False
  | i => RemainingGenerationIndex i

theorem model_twoGenerated_or_remaining_without_typeA (i : CFSG.Index)
    (hn : ¬IsMulCommutative i.Model) :
    TwoGenerated i.Model∨RemainingGenerationIndexWithoutTypeA i := by
  cases i <;> try exact model_twoGenerated_or_remaining _ hn
  case A r q hr hs => exact Or.inl (typeA_twoGenerated r q hr hs)

/-- The exact finite-simple generation reduction after discharging the
whole pinned type-A family, including its dimension-two small guards. -/
theorem finiteSimpleTwoGeneratorBound_of_cfsg_and_remaining_non_typeA_models
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      IsCenterless i.Model→RemainingGenerationIndexWithoutTypeA i→TwoGenerated i.Model) :
    ∀ (G : Type) [Group G] [Finite G],IsSimpleGroup G→IsCenterless G→TwoGenerated G := by
  apply finiteSimpleTwoGeneratorBound_of_cfsg_and_remaining_models hCFSG
  intro i _ _ hc hi
  cases i <;> try exact remaining _ hc hi
  case A => exact typeA_twoGenerated _ _ (by assumption) (by assumption)

end SymmetricSubgroupAsymptotics.CFSGReduction
