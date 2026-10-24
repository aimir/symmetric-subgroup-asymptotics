import SymmetricSubgroupAsymptotics.PrimitiveAllDegreeReeGTwoCFSGReduction
import SymmetricSubgroupAsymptotics.PrimitiveSocleTrialityCompleteClassBound

/-! Every original triality field order at least three leaves the bounded
primitive class-count frontier. Binary triality remains explicit, with
the actual raw socle and both degree forms preserved. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAllDegreeTrialityHeisenbergCFSGReduction
open PrimitiveSocleRawStructure CFSGReduction
open PrimitiveAllDegreeSubnormalCFSGReduction PrimitiveLargeSubnormalCFSGReduction

def RemainingBoundedPrimitiveParameters : CFSG.Index → Prop
  | .trialityD4 q => q.order=2 ∧
      PrimitiveAllDegreeReeGTwoCFSGReduction.RemainingBoundedPrimitiveParameters (.trialityD4 q)
  | i => PrimitiveAllDegreeReeGTwoCFSGReduction.RemainingBoundedPrimitiveParameters i

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
  rcases PrimitiveAllDegreeReeGTwoCFSGReduction.primitive_subnormal_cube_or_actual_remaining_parameters
    hCFSG G X hn H hH with hc | ⟨D,i,⟨e⟩,hstate,hform⟩
  · exact Or.inl hc
  · rcases hstate with ⟨hsmall,hremaining⟩ | hlarge
    · cases i
      case trialityD4 q =>
        by_cases hq : 3 ≤ q.order
        · exact Or.inl (D.subgroup_class_cube_le_of_triality_field_ge_three q hq e H)
        · have htwo : 2 ≤ q.order := q.prime_isPrime.two_le.trans
            (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
          exact Or.inr ⟨D,.trialityD4 q,⟨e⟩,Or.inl ⟨hsmall,⟨by omega,hremaining⟩⟩,hform⟩
      all_goals exact Or.inr ⟨D,_,⟨e⟩,Or.inl ⟨hsmall,hremaining⟩,hform⟩
    · exact Or.inr ⟨D,i,⟨e⟩,Or.inr hlarge,hform⟩

end SymmetricSubgroupAsymptotics.PrimitiveAllDegreeTrialityHeisenbergCFSGReduction
