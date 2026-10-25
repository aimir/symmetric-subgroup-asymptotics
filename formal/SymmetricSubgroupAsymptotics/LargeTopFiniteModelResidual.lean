import SymmetricSubgroupAsymptotics.LargeTopLieSmallFibreClassBound
import SymmetricSubgroupAsymptotics.LargeTopAlternatingSmallFibreClassBound

/-! The actual large primitive top of a binary or ternary block action.
The affine, power, Lie and alternating branches have proved bounds.
Only the literal Tits or sporadic source may remain, together with the
same D/K index form and both failed component-order budgets. This is a
residual theorem, not a claim that the remaining sources satisfy GM. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.LargeTopFiniteModelResidual
open PrimitiveSocleRawStructure OriginalBlockClassBound

def RemainingFiniteSimpleType : CFSG.Index → Prop
  | .tits | .sporadic _ => True
  | _ => False

private theorem alternating_of_remaining_not_finite (i : CFSG.Index)
    (hi : CFSGModelComponentIndexOrderBudget.RemainingSimpleType i)
    (hf : ¬ RemainingFiniteSimpleType i) :
    ∃ (m : ℕ) (hm : 5 ≤ m), i = .alternating m hm := by
  cases i <;> simp_all [CFSGModelComponentIndexOrderBudget.RemainingSimpleType,
    RemainingFiniteSimpleType]

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem primitive_top_cube_or_actual_finite_model
    (hCFSG : CFSG.CFSGClassification)
    (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (c : ℕ) (hc : c = 2 ∨ c = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x) = c)
    (hn : 4096 ≤ Nat.card X)
    (hprimitive : MulAction.IsPreprimitive (Top (A := A) (X := X)) X) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) ∨
      ∃ D : NonaffineData (Top (A := A) (X := X)) X,
        ∃ i : CFSG.Index, RemainingFiniteSimpleType i ∧ Nonempty (D.Simple ≃* i.Model) ∧
          ∃ K : Subgroup D.Simple, K ≠ ⊤ ∧ Nat.card X = K.index ^ D.factorCount ∧
            K.index ^ (4 * Nat.log 2 K.index + 23) <
              Nat.card D.Simple * Nat.card (Outer D.Simple) ∧
            K.index ^ 66 < Nat.card D.Simple * Nat.card (Outer D.Simple) := by
  rcases LargeTopLieSmallFibreClassBound.primitive_top_cube_or_actual_remaining_model
    hCFSG b hb c hc hsize hn hprimitive with h | ⟨D,i,hi,he,K,hK,hdegree,hlog,hbound⟩
  · exact Or.inl h
  · by_cases hf : RemainingFiniteSimpleType i
    · exact Or.inr ⟨D,i,hf,he,K,hK,hdegree,hlog,hbound⟩
    · obtain ⟨m,hm,rfl⟩ := alternating_of_remaining_not_finite i hi hf
      obtain ⟨e⟩ := he
      exact Or.inl
        (LargeTopAlternatingSmallFibreClassBound.class_cube_le_of_alternating_top
          b hb c hc hsize hn D m hm e K hK hdegree)

end SymmetricSubgroupAsymptotics.LargeTopFiniteModelResidual
