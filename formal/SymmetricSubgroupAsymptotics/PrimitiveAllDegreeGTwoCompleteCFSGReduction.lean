import SymmetricSubgroupAsymptotics.PrimitiveAllDegreeReeFFourTailCFSGReduction
import SymmetricSubgroupAsymptotics.PrimitiveSocleGTwoFieldThreeClassBound

/-! The entire original G2 family is discharged. Every previously proved
classical, exceptional, triality and Ree-tail closure is preserved, for
all socle factors and both actual primitive degree forms. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAllDegreeGTwoCompleteCFSGReduction
open PrimitiveSocleRawStructure CFSGReduction
open PrimitiveAllDegreeSubnormalCFSGReduction PrimitiveLargeSubnormalCFSGReduction

def RemainingBoundedPrimitiveParameters : CFSG.Index → Prop
  | .G2 _ _ => False
  | i => PrimitiveAllDegreeReeFFourTailCFSGReduction.RemainingBoundedPrimitiveParameters i

theorem primitive_subnormal_cube_or_actual_remaining_parameters
    (hCFSG : CFSG.CFSGClassification)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (hn : 4 ≤ Nat.card X) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) ∨
      ∃ D : NonaffineData G X, ∃ i : CFSG.Index,
        Nonempty (D.Simple ≃* i.Model) ∧
        ((Nat.card X < 1024 ∧ RemainingBoundedPrimitiveParameters i) ∨
          (1024 ≤ Nat.card X ∧
            PrimitiveAllDegreeReeFFourTailCFSGReduction.RemainingLargePrimitiveParameters i)) ∧
        ((∃ K : Subgroup D.Simple, K ≠ ⊤ ∧ Nat.card X = K.index^D.factorCount) ∨
          (∃ a : ℕ, D.factorCount ≤ 2*a ∧ Nat.card X = (Nat.card D.Simple)^a)) := by
  rcases PrimitiveAllDegreeReeFFourTailCFSGReduction.primitive_subnormal_cube_or_actual_remaining_parameters
    hCFSG G X hn H hH with hc | ⟨D,i,⟨e⟩,hstate,hform⟩
  · exact Or.inl hc
  · rcases hstate with ⟨hsmall,hremaining⟩ | hlarge
    · cases i
      case G2 q hs =>
        have hq4 : q.order≠4 := hremaining.1
        have hq5 : q.order<5 := hremaining.2.1
        have htwo : 2≤q.order := by
          change 2≤q.prime^q.exponent
          exact q.prime_isPrime.two_le.trans
            (Nat.le_self_pow q.exponent_pos.ne' q.prime)
        have hq3 : q.order=3 := by omega
        exact Or.inl (D.subgroup_class_cube_le_of_gTwo_field_three q hq3 e H)
      all_goals exact Or.inr ⟨D,_,⟨e⟩,Or.inl ⟨hsmall,hremaining⟩,hform⟩
    · exact Or.inr ⟨D,i,⟨e⟩,Or.inr hlarge,hform⟩

end SymmetricSubgroupAsymptotics.PrimitiveAllDegreeGTwoCompleteCFSGReduction
