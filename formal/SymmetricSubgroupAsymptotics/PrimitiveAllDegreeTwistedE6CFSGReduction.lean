import SymmetricSubgroupAsymptotics.PrimitiveAllDegreeClassicalCFSGReduction
import SymmetricSubgroupAsymptotics.PrimitiveSocleTwistedE6CompleteClassBound

/-! The actual primitive class-count frontier after the fixed-field
Heisenberg bound discharges the entire twisted-E6 family. The original
socle, both degree forms and the subnormal subgroup are retained.
Other exceptional families, Tits and sporadic cases remain explicit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAllDegreeTwistedE6CFSGReduction
open PrimitiveSocleRawStructure CFSGReduction
open PrimitiveAllDegreeSubnormalCFSGReduction PrimitiveLargeSubnormalCFSGReduction

def RemainingBoundedPrimitiveParameters : CFSG.Index → Prop
  | .twistedE6 _ => False
  | i => PrimitiveAllDegreeClassicalCFSGReduction.RemainingBoundedPrimitiveParameters i

theorem primitive_subnormal_cube_or_actual_remaining_parameters
    (hCFSG : CFSG.CFSGClassification)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (hn : 4 ≤ Nat.card X) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) ∨
      ∃ D : NonaffineData G X, ∃ i : CFSG.Index,
        Nonempty (D.Simple ≃* i.Model) ∧
        ((Nat.card X < 1024 ∧ RemainingBoundedPrimitiveParameters i) ∨
          (1024 ≤ Nat.card X ∧ RemainingLargePrimitiveSimpleType i)) ∧
        ((∃ K : Subgroup D.Simple, K ≠ ⊤ ∧ Nat.card X = K.index^D.factorCount) ∨
          (∃ a : ℕ, D.factorCount ≤ 2*a ∧ Nat.card X = (Nat.card D.Simple)^a)) := by
  rcases PrimitiveAllDegreeClassicalCFSGReduction.primitive_subnormal_cube_or_actual_remaining_parameters
    hCFSG G X hn H hH with hc | ⟨D,i,⟨e⟩,hstate,hform⟩
  · exact Or.inl hc
  · rcases hstate with ⟨hsmall,hremaining⟩ | hlarge
    · cases i
      case twistedE6 q =>
        exact Or.inl (D.subgroup_class_cube_le_of_twistedE6_allDegrees q e H)
      all_goals exact Or.inr ⟨D,_,⟨e⟩,Or.inl ⟨hsmall,hremaining⟩,hform⟩
    · exact Or.inr ⟨D,i,⟨e⟩,Or.inr hlarge,hform⟩

end SymmetricSubgroupAsymptotics.PrimitiveAllDegreeTwistedE6CFSGReduction
