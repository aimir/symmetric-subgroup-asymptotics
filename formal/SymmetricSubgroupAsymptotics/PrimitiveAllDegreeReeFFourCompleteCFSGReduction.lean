import SymmetricSubgroupAsymptotics.PrimitiveAllDegreeReeFFourMiddleSuzukiCFSGReduction
import SymmetricSubgroupAsymptotics.PrimitiveSocleReeFFourFieldEightClassBound

/-! The entire original positive-parameter ReeF4 primitive class branch.
Only the exact Tits and sporadic model tags remain, with the original
action, subnormal subgroup and degree forms retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAllDegreeReeFFourCompleteCFSGReduction
open PrimitiveSocleRawStructure

def RemainingFiniteSimpleType : CFSG.Index → Prop
  | .tits | .sporadic _ => True
  | _ => False

theorem primitive_subnormal_cube_or_finite_model
    (hCFSG : CFSG.CFSGClassification)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (hn : 4 ≤ Nat.card X) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) ∨
      ∃ D : NonaffineData G X, ∃ i : CFSG.Index,
        Nonempty (D.Simple ≃* i.Model) ∧ RemainingFiniteSimpleType i ∧
        ((∃ K : Subgroup D.Simple, K≠⊤ ∧ Nat.card X=K.index^D.factorCount) ∨
          (∃ a : ℕ, D.factorCount≤2*a ∧ Nat.card X=(Nat.card D.Simple)^a)) := by
  rcases PrimitiveAllDegreeReeFFourMiddleSuzukiCFSGReduction.primitive_subnormal_cube_or_finite_model
    hCFSG G X hn H hH with hc | ⟨D,i,⟨e⟩,hi,hform⟩
  · exact Or.inl hc
  · cases i
    case reeF4 m hm =>
      have hone : m=1 := hi
      have e₁ : D.Simple ≃* CFSG.Models.ReeF4 1 := by
        exact (congrArg (fun t : ℕ => D.Simple ≃* CFSG.Models.ReeF4 t) hone).mp e
      exact Or.inl (D.subgroup_class_cube_le_of_reeFFour_field_eight e₁ H)
    all_goals exact Or.inr ⟨D,_,⟨e⟩,hi,hform⟩

end SymmetricSubgroupAsymptotics.PrimitiveAllDegreeReeFFourCompleteCFSGReduction
