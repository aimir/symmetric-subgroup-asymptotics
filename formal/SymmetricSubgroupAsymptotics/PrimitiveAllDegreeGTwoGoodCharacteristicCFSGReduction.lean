import SymmetricSubgroupAsymptotics.PrimitiveAllDegreeTrialityHeisenbergCFSGReduction
import SymmetricSubgroupAsymptotics.PrimitiveSocleGTwoGoodCharacteristicClassBound

/-! The actual bounded primitive frontier after good-characteristic G2
fields of order at least five are discharged. The surviving characteristic
three and small-field states keep the original socle and degree data. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAllDegreeGTwoGoodCharacteristicCFSGReduction
open PrimitiveSocleRawStructure CFSGReduction
open PrimitiveAllDegreeSubnormalCFSGReduction PrimitiveLargeSubnormalCFSGReduction

def RemainingBoundedPrimitiveParameters : CFSG.Index → Prop
  | .G2 q hs => (q.order<5 ∨ q.prime=3) ∧
      PrimitiveAllDegreeTrialityHeisenbergCFSGReduction.RemainingBoundedPrimitiveParameters (.G2 q hs)
  | i => PrimitiveAllDegreeTrialityHeisenbergCFSGReduction.RemainingBoundedPrimitiveParameters i

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
  rcases PrimitiveAllDegreeTrialityHeisenbergCFSGReduction.primitive_subnormal_cube_or_actual_remaining_parameters
    hCFSG G X hn H hH with hc | ⟨D,i,⟨e⟩,hstate,hform⟩
  · exact Or.inl hc
  · rcases hstate with ⟨hsmall,hremaining⟩ | hlarge
    · cases i
      case G2 q hs =>
        by_cases hq : 5 ≤ q.order
        · by_cases hchar : q.prime=3
          · exact Or.inr ⟨D,.G2 q hs,⟨e⟩,Or.inl ⟨hsmall,⟨Or.inr hchar,hremaining⟩⟩,hform⟩
          · exact Or.inl (D.subgroup_class_cube_le_of_gTwo_good_characteristic q hq hchar e H)
        · exact Or.inr ⟨D,.G2 q hs,⟨e⟩,Or.inl ⟨hsmall,⟨Or.inl (by omega),hremaining⟩⟩,hform⟩
      all_goals exact Or.inr ⟨D,_,⟨e⟩,Or.inl ⟨hsmall,hremaining⟩,hform⟩
    · exact Or.inr ⟨D,i,⟨e⟩,Or.inr hlarge,hform⟩

end SymmetricSubgroupAsymptotics.PrimitiveAllDegreeGTwoGoodCharacteristicCFSGReduction
