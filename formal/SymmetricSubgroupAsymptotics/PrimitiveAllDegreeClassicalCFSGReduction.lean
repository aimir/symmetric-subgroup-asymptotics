import SymmetricSubgroupAsymptotics.PrimitiveAllDegreePrimaryClassCFSGReduction
import SymmetricSubgroupAsymptotics.PrimitiveSocleOrthogonalBinaryRankFourClassBound

/-! Every classical family is discharged on the original primitive
action. The only remaining models are exceptional Lie types, Tits and
sporadic types. The exact raw socle and both degree forms are retained;
this is not the complete primitive or global class-count theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAllDegreeClassicalCFSGReduction
open PrimitiveSocleRawStructure CFSGReduction
open PrimitiveAllDegreeSubnormalCFSGReduction PrimitiveLargeSubnormalCFSGReduction

def RemainingBoundedPrimitiveParameters : CFSG.Index → Prop
  | .D _ _ _ | .twistedD _ _ _ => False
  | i => PrimitiveAllDegreePrimaryClassCFSGReduction.RemainingBoundedPrimitiveParameters i

private theorem binary_order_eq_two (q : CFSG.PrimePower) (hthree : ¬3 ≤ q.order) :
    q.order = 2 := by
  have hqlo : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  omega

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
  rcases PrimitiveAllDegreePrimaryClassCFSGReduction.primitive_subnormal_cube_or_actual_remaining_parameters
    hCFSG G X hn H hH with hc | ⟨D,i,⟨e⟩,hstate,hform⟩
  · exact Or.inl hc
  · rcases hstate with ⟨hsmall,hremaining⟩ | hlarge
    · cases i
      case D r q hr =>
        change _ ∧ _ ∧ ¬(3 ≤ q.order ∨ 5 ≤ r) at hremaining
        obtain ⟨_,_,hw⟩ := hremaining
        have hr4 : r = 4 := by omega
        subst r
        have hq := binary_order_eq_two q (fun h => hw (Or.inl h))
        exact Or.inl (D.subnormal_class_cube_le_of_typeD_binary_rank_four q hq e H hH)
      case twistedD r q hr =>
        change _ ∧ _ ∧ ¬(3 ≤ q.order ∨ 5 ≤ r) at hremaining
        obtain ⟨_,_,hw⟩ := hremaining
        have hr4 : r = 4 := by omega
        subst r
        have hq := binary_order_eq_two q (fun h => hw (Or.inl h))
        exact Or.inl (D.subnormal_class_cube_le_of_typeTwistedD_binary_rank_four q hq e H hH)
      all_goals exact Or.inr ⟨D,_,⟨e⟩,Or.inl ⟨hsmall,hremaining⟩,hform⟩
    · exact Or.inr ⟨D,i,⟨e⟩,Or.inr hlarge,hform⟩

end SymmetricSubgroupAsymptotics.PrimitiveAllDegreeClassicalCFSGReduction
