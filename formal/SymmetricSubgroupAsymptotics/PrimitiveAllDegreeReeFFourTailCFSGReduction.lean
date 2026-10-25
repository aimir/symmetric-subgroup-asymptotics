import SymmetricSubgroupAsymptotics.PrimitiveAllDegreeTrialityCompleteCFSGReduction
import SymmetricSubgroupAsymptotics.PrimitiveSocleReeFFourOrderCubeTailClassBound

/-! The entire Ree F4 parameter tail m>=4 is discharged in both degree
regimes. Remaining Ree F4 witnesses have exactly m=1,2,3 by the Index
positivity guard. Every other actual model and raw degree witness is
inherited from the checked complete-triality frontier. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAllDegreeReeFFourTailCFSGReduction
open PrimitiveSocleRawStructure CFSGReduction
open PrimitiveAllDegreeSubnormalCFSGReduction PrimitiveLargeSubnormalCFSGReduction

def RemainingBoundedPrimitiveParameters : CFSG.Index → Prop
  | .reeF4 m _ => m≤3
  | i => PrimitiveAllDegreeTrialityCompleteCFSGReduction.RemainingBoundedPrimitiveParameters i

def RemainingLargePrimitiveParameters : CFSG.Index → Prop
  | .reeF4 m _ => m≤3
  | i => RemainingLargePrimitiveSimpleType i

theorem primitive_subnormal_cube_or_actual_remaining_parameters
    (hCFSG : CFSG.CFSGClassification)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (hn : 4≤Nat.card X) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card X-1) ∨
      ∃ D : NonaffineData G X, ∃ i : CFSG.Index,
        Nonempty (D.Simple ≃* i.Model) ∧
        ((Nat.card X<1024 ∧ RemainingBoundedPrimitiveParameters i) ∨
          (1024≤Nat.card X ∧ RemainingLargePrimitiveParameters i)) ∧
        ((∃ K : Subgroup D.Simple, K≠⊤ ∧ Nat.card X=K.index^D.factorCount) ∨
          (∃ a : ℕ, D.factorCount≤2*a ∧ Nat.card X=(Nat.card D.Simple)^a)) := by
  rcases PrimitiveAllDegreeTrialityCompleteCFSGReduction.primitive_subnormal_cube_or_actual_remaining_parameters
    hCFSG G X hn H hH with hc | ⟨D,i,⟨e⟩,hstate,hform⟩
  · exact Or.inl hc
  · cases i
    case reeF4 m hm =>
      by_cases htail : 4 ≤ m
      · exact Or.inl (D.subgroup_class_cube_le_of_reeFFour_order_tail m htail e H)
      · have hsmallm : m≤3 := by omega
        rcases hstate with hs | hl
        · exact Or.inr ⟨D,.reeF4 m hm,⟨e⟩,Or.inl ⟨hs.1,hsmallm⟩,hform⟩
        · exact Or.inr ⟨D,.reeF4 m hm,⟨e⟩,Or.inr ⟨hl.1,hsmallm⟩,hform⟩
    all_goals exact Or.inr ⟨D,_,⟨e⟩,hstate,hform⟩

end SymmetricSubgroupAsymptotics.PrimitiveAllDegreeReeFFourTailCFSGReduction
