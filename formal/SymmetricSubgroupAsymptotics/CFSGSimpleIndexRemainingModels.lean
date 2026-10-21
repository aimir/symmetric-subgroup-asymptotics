import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import SymmetricSubgroupAsymptotics.CFSGAlternatingOuterBound

/-! The alternating family is discharged from the concrete simple-index
reduction. The remaining hypothesis below refers only to other literal
models; it is an explicit open reduction, not a CFSG-only endpoint. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

def ModelSimpleIndexBounds (i : CFSG.Index) : Prop :=
  ∀ ell : ℕ, LeastProperIndex i.Model ell →
    ell ^ 2 < Nat.card i.Model ∧
      (Nat.card (Outer i.Model) : ℝ) ≤ 3 * Real.logb 2 ell

def RemainingSimpleIndexModel : CFSG.Index → Prop
  | .cyclic _ _ => False
  | .alternating _ _ => False
  | _ => True

theorem simpleIndex_model_or_remaining (i : CFSG.Index) :
    ¬ IsMulCommutative i.Model →
      ModelSimpleIndexBounds i ∨ RemainingSimpleIndexModel i := by
  cases i <;> try exact fun _ => Or.inr trivial
  case cyclic p hp =>
    intro hn
    exfalso
    apply hn
    change IsMulCommutative (Multiplicative (ZMod p))
    infer_instance
  case alternating n hn =>
    intro _
    exact Or.inl (CFSGAlternatingOuterBound.simpleIndexBounds n hn)

theorem publishedSimpleIndexBounds_of_cfsg_and_remaining_models
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingSimpleIndexModel i →
        ModelSimpleIndexBounds i) : PublishedSimpleIndexBounds := by
  apply publishedSimpleIndexBounds_of_models hCFSG
  intro i _ _ hn
  rcases simpleIndex_model_or_remaining i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
