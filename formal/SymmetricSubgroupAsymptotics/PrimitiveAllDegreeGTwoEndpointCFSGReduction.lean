import SymmetricSubgroupAsymptotics.PrimitiveAllDegreeGTwoGoodCharacteristicCFSGReduction
import SymmetricSubgroupAsymptotics.PrimitiveSocleGTwoEndpointClassBound

/-! The original G2 bounded frontier after the characteristic-three
endpoint argument. Only fields of order three and four can remain in
that family; all actual simple factors and degree forms are preserved. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAllDegreeGTwoEndpointCFSGReduction
open PrimitiveSocleRawStructure CFSGReduction
open PrimitiveAllDegreeSubnormalCFSGReduction PrimitiveLargeSubnormalCFSGReduction

theorem char_three_ge_nine_of_ge_five (q : CFSG.PrimePower)
    (hq : 5 ≤ q.order) (hchar : q.prime=3) : 9 ≤ q.order := by
  have he : 2 ≤ q.exponent := by
    by_contra h
    have he1 : q.exponent=1 := by have hpos:=q.exponent_pos; omega
    have ho : q.order=3 := by change q.prime^q.exponent=3; rw [hchar,he1,pow_one]
    omega
  change 3^2 ≤ q.prime^q.exponent
  rw [hchar]
  exact Nat.pow_le_pow_right (by decide) he

def RemainingBoundedPrimitiveParameters : CFSG.Index → Prop
  | .G2 q hs => q.order<5 ∧
      PrimitiveAllDegreeGTwoGoodCharacteristicCFSGReduction.RemainingBoundedPrimitiveParameters (.G2 q hs)
  | i => PrimitiveAllDegreeGTwoGoodCharacteristicCFSGReduction.RemainingBoundedPrimitiveParameters i

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
  rcases PrimitiveAllDegreeGTwoGoodCharacteristicCFSGReduction.primitive_subnormal_cube_or_actual_remaining_parameters
    hCFSG G X hn H hH with hc | ⟨D,i,⟨e⟩,hstate,hform⟩
  · exact Or.inl hc
  · rcases hstate with ⟨hsmall,hremaining⟩ | hlarge
    · cases i
      case G2 q hs =>
        by_cases hq : 5 ≤ q.order
        · have hchar : q.prime=3 := hremaining.1.resolve_left (by omega)
          exact Or.inl (D.subgroup_class_cube_le_of_gTwo_char_three q
            (char_three_ge_nine_of_ge_five q hq hchar) hchar e H)
        · exact Or.inr ⟨D,.G2 q hs,⟨e⟩,Or.inl ⟨hsmall,⟨by omega,hremaining⟩⟩,hform⟩
      all_goals exact Or.inr ⟨D,_,⟨e⟩,Or.inl ⟨hsmall,hremaining⟩,hform⟩
    · exact Or.inr ⟨D,i,⟨e⟩,Or.inr hlarge,hform⟩

end SymmetricSubgroupAsymptotics.PrimitiveAllDegreeGTwoEndpointCFSGReduction
