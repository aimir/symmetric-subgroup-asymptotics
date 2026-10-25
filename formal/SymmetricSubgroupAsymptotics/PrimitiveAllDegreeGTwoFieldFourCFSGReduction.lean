import SymmetricSubgroupAsymptotics.PrimitiveAllDegreeFFourCompleteCFSGReduction
import SymmetricSubgroupAsymptotics.PrimitiveSocleGTwoFieldFourClassBound

/-! The original G2 field-four case is discharged. The previous full
F4 and characteristic-three endpoint frontiers are retained; only the
field-three G2 parameter survives this refinement. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAllDegreeGTwoFieldFourCFSGReduction
open PrimitiveSocleRawStructure CFSGReduction
open PrimitiveAllDegreeSubnormalCFSGReduction PrimitiveLargeSubnormalCFSGReduction

def RemainingBoundedPrimitiveParameters : CFSG.Index → Prop
  | .G2 q hs => q.order≠4 ∧
      PrimitiveAllDegreeFFourCompleteCFSGReduction.RemainingBoundedPrimitiveParameters (.G2 q hs)
  | i => PrimitiveAllDegreeFFourCompleteCFSGReduction.RemainingBoundedPrimitiveParameters i

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
  rcases PrimitiveAllDegreeFFourCompleteCFSGReduction.primitive_subnormal_cube_or_actual_remaining_parameters
    hCFSG G X hn H hH with hc | ⟨D,i,⟨e⟩,hstate,hform⟩
  · exact Or.inl hc
  · rcases hstate with ⟨hsmall,hremaining⟩ | hlarge
    · cases i
      case G2 q hs =>
        by_cases hq : q.order=4
        · exact Or.inl (D.subgroup_class_cube_le_of_gTwo_field_four q hq e H)
        · exact Or.inr ⟨D,.G2 q hs,⟨e⟩,Or.inl ⟨hsmall,⟨hq,hremaining⟩⟩,hform⟩
      all_goals exact Or.inr ⟨D,_,⟨e⟩,Or.inl ⟨hsmall,hremaining⟩,hform⟩
    · exact Or.inr ⟨D,i,⟨e⟩,Or.inr hlarge,hform⟩

end SymmetricSubgroupAsymptotics.PrimitiveAllDegreeGTwoFieldFourCFSGReduction
