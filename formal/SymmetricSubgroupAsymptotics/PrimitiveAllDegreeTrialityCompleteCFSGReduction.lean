import SymmetricSubgroupAsymptotics.PrimitiveAllDegreeGTwoFieldFourCFSGReduction
import SymmetricSubgroupAsymptotics.PrimitiveSocleTrialityBinaryClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleTrialityCompleteClassBound

/-! The entire original triality family is discharged, including its
binary regular-module source. The full F4 and field-four G2 closures
are preserved for every other actual model and degree form. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAllDegreeTrialityCompleteCFSGReduction
open PrimitiveSocleRawStructure CFSGReduction
open PrimitiveAllDegreeSubnormalCFSGReduction PrimitiveLargeSubnormalCFSGReduction

def RemainingBoundedPrimitiveParameters : CFSG.Index → Prop
  | .trialityD4 _ => False
  | i => PrimitiveAllDegreeGTwoFieldFourCFSGReduction.RemainingBoundedPrimitiveParameters i

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
  rcases PrimitiveAllDegreeGTwoFieldFourCFSGReduction.primitive_subnormal_cube_or_actual_remaining_parameters
    hCFSG G X hn H hH with hc | ⟨D,i,⟨e⟩,hstate,hform⟩
  · exact Or.inl hc
  · rcases hstate with ⟨hsmall,hremaining⟩ | hlarge
    · cases i
      case trialityD4 q =>
        by_cases hq : q.order=2
        · exact Or.inl (D.subgroup_class_cube_le_of_triality_binary q hq e H)
        · have htwo : 2≤q.order := by
            change 2≤q.prime^q.exponent
            exact q.prime_isPrime.two_le.trans
              (Nat.le_self_pow q.exponent_pos.ne' q.prime)
          exact Or.inl (D.subgroup_class_cube_le_of_triality_field_ge_three q
            (by omega) e H)
      all_goals exact Or.inr ⟨D,_,⟨e⟩,Or.inl ⟨hsmall,hremaining⟩,hform⟩
    · exact Or.inr ⟨D,i,⟨e⟩,Or.inr hlarge,hform⟩

end SymmetricSubgroupAsymptotics.PrimitiveAllDegreeTrialityCompleteCFSGReduction
