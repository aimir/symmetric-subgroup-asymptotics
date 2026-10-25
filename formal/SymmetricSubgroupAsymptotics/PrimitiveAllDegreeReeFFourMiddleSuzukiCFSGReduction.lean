import SymmetricSubgroupAsymptotics.PrimitiveFiniteModelClassResidual
import SymmetricSubgroupAsymptotics.PrimitiveSocleReeFFourMiddleSuzukiClassBound

/-! The actual middle Suzuki Borel discharges every Ree F4 m>=2.
The explicit finite-model residual retains only Ree F4 m=1, Tits and
sporadic models, with the same original socle, subgroup and degree data. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAllDegreeReeFFourMiddleSuzukiCFSGReduction
open PrimitiveSocleRawStructure

def RemainingFiniteSimpleType : CFSG.Index → Prop
  | .reeF4 m _ => m = 1
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
        ((∃ K : Subgroup D.Simple, K ≠ ⊤ ∧ Nat.card X = K.index^D.factorCount) ∨
          (∃ a : ℕ, D.factorCount ≤ 2*a ∧ Nat.card X = (Nat.card D.Simple)^a)) := by
  rcases PrimitiveFiniteModelClassResidual.primitive_subnormal_cube_or_finite_model
    hCFSG G X hn H hH with hc | ⟨D,i,⟨e⟩,hi,hform⟩
  · exact Or.inl hc
  · cases i
    case reeF4 m hm =>
      by_cases htail : 2 ≤ m
      · exact Or.inl (D.subgroup_class_cube_le_of_reeFFour_middle_suzuki m htail e H)
      · have hone : m = 1 := by omega
        exact Or.inr ⟨D,.reeF4 m hm,⟨e⟩,hone,hform⟩
    all_goals exact Or.inr ⟨D,_,⟨e⟩,hi,hform⟩

end SymmetricSubgroupAsymptotics.PrimitiveAllDegreeReeFFourMiddleSuzukiCFSGReduction
