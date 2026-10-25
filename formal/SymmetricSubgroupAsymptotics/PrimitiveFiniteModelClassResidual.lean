import SymmetricSubgroupAsymptotics.PrimitiveAllDegreeGTwoCompleteCFSGReduction
import SymmetricSubgroupAsymptotics.PrimitiveSocleReeGTwoCompleteClassBound

/-! The remaining primitive class problem is supported on three original
Ree F4 models, the original Tits model and the twenty-six original
sporadic models. The residual callback below is explicit and unproved.
All raw socle factors, original subnormal subgroups and both actual
primitive degree forms remain in its statement. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveFiniteModelClassResidual
open PrimitiveSocleRawStructure

def RemainingFiniteSimpleType : CFSG.Index → Prop
  | .reeF4 m _ => m=1 ∨ m=2 ∨ m=3
  | .tits | .sporadic _ => True
  | _ => False

theorem remaining_bounded_iff (i : CFSG.Index) :
    PrimitiveAllDegreeGTwoCompleteCFSGReduction.RemainingBoundedPrimitiveParameters i ↔
      RemainingFiniteSimpleType i := by
  cases i <;> simp [RemainingFiniteSimpleType,
    PrimitiveAllDegreeGTwoCompleteCFSGReduction.RemainingBoundedPrimitiveParameters,
    PrimitiveAllDegreeReeFFourTailCFSGReduction.RemainingBoundedPrimitiveParameters,
    PrimitiveAllDegreeTrialityCompleteCFSGReduction.RemainingBoundedPrimitiveParameters,
    PrimitiveAllDegreeGTwoFieldFourCFSGReduction.RemainingBoundedPrimitiveParameters,
    PrimitiveAllDegreeFFourCompleteCFSGReduction.RemainingBoundedPrimitiveParameters,
    PrimitiveAllDegreeGTwoEndpointCFSGReduction.RemainingBoundedPrimitiveParameters,
    PrimitiveAllDegreeGTwoGoodCharacteristicCFSGReduction.RemainingBoundedPrimitiveParameters,
    PrimitiveAllDegreeTrialityHeisenbergCFSGReduction.RemainingBoundedPrimitiveParameters,
    PrimitiveAllDegreeReeGTwoCFSGReduction.RemainingBoundedPrimitiveParameters,
    PrimitiveAllDegreeFFourHeisenbergCFSGReduction.RemainingBoundedPrimitiveParameters,
    PrimitiveAllDegreeSuzukiCFSGReduction.RemainingBoundedPrimitiveParameters,
    PrimitiveAllDegreeTwistedE6CFSGReduction.RemainingBoundedPrimitiveParameters,
    PrimitiveAllDegreeClassicalCFSGReduction.RemainingBoundedPrimitiveParameters,
    PrimitiveAllDegreePrimaryClassCFSGReduction.RemainingBoundedPrimitiveParameters,
    PrimitiveAllDegreeIsometryCFSGReduction.RemainingBoundedPrimitiveParameters] <;> omega

theorem remaining_large_cases (i : CFSG.Index)
    (hi : PrimitiveAllDegreeReeFFourTailCFSGReduction.RemainingLargePrimitiveParameters i) :
    RemainingFiniteSimpleType i ∨ ∃ (m : ℕ) (hm : 1 ≤ m), i = .reeG2 m hm := by
  cases i
  case reeG2 m hm => exact Or.inr ⟨m,hm,rfl⟩
  all_goals apply Or.inl
  all_goals simp [RemainingFiniteSimpleType,
    PrimitiveAllDegreeReeFFourTailCFSGReduction.RemainingLargePrimitiveParameters,
    PrimitiveLargeSubnormalCFSGReduction.RemainingLargePrimitiveSimpleType] at hi ⊢ <;> omega

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
  rcases PrimitiveAllDegreeGTwoCompleteCFSGReduction.primitive_subnormal_cube_or_actual_remaining_parameters
    hCFSG G X hn H hH with hc | ⟨D,i,e,hstate,hform⟩
  · exact Or.inl hc
  · rcases hstate with hs | hl
    · exact Or.inr ⟨D,i,e,(remaining_bounded_iff i).mp hs.2,hform⟩
    · rcases remaining_large_cases i hl.2 with hi | ⟨m,hm,rfl⟩
      · exact Or.inr ⟨D,i,e,hi,hform⟩
      · obtain ⟨e⟩ := e
        exact Or.inl (D.subgroup_class_cube_le_of_reeGTwo_allDegrees m hm e H)

/-- Explicit remaining actual-model obligation. This is not an installed
finite catalogue, and it does not bound arbitrary quotient actions by
substituting an abstract isomorphism type. -/
def FiniteActualModelResidual : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X],
    4 ≤ Nat.card X → ∀ (D : NonaffineData G X) (i : CFSG.Index),
    RemainingFiniteSimpleType i → (D.Simple ≃* i.Model) →
    ∀ H : Subgroup G, H.IsSubnormal →
    ((∃ K : Subgroup D.Simple, K ≠ ⊤ ∧ Nat.card X = K.index^D.factorCount) ∨
      (∃ a : ℕ, D.factorCount ≤ 2*a ∧ Nat.card X = (Nat.card D.Simple)^a)) →
      Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1)

theorem primitive_class_cube_of_finite_residual (hCFSG : CFSG.CFSGClassification)
    (hResidual : FiniteActualModelResidual)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (hn : 4 ≤ Nat.card X) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  rcases primitive_subnormal_cube_or_finite_model hCFSG G X hn H hH with hc | ⟨D,i,⟨e⟩,hi,hform⟩
  · exact hc
  · exact hResidual G X hn D i hi e H hH hform

end SymmetricSubgroupAsymptotics.PrimitiveFiniteModelClassResidual
