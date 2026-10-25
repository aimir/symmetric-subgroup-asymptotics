import SymmetricSubgroupAsymptotics.PrimitiveLargeOrderFiniteResidual
import SymmetricSubgroupAsymptotics.LargeAlternatingSmallFibreSubnormalGap
import SymmetricSubgroupAsymptotics.LargeTopFiniteModelResidual

/-! An actual large primitive intermediate top gives the stronger
subnormal source gap, except for literal Tits/sporadic component data.
Both raw index budgets and the original subgroup/action are retained.
No class-count callback or primitive outer-top assumption is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.LargePrimitiveIntermediateSubnormalGapResidual
open PrimitiveSocleRawStructure OriginalBlockClassBound LargeTopFiniteModelResidual

private theorem alternating_of_remaining_not_finite (i : CFSG.Index)
    (hi : CFSGModelComponentIndexOrderBudget.RemainingSimpleType i)
    (hf : ¬ RemainingFiniteSimpleType i) :
    ∃ (m : ℕ) (hm : 5 ≤ m), i = .alternating m hm := by
  cases i <;> simp_all [CFSGModelComponentIndexOrderBudget.RemainingSimpleType,
    RemainingFiniteSimpleType]

theorem subnormal_gap_or_actual_finite_model
    (hCFSG : CFSG.CFSGClassification)
    {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]
    (b : Ω → X) (hb : ∀ (g : A) (ω : Ω), b (g • ω) = g • b ω)
    (c : ℕ) (hc : c = 2 ∨ c = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x) = c)
    (hn : 4096 ≤ Nat.card X)
    (hprimitive : MulAction.IsPreprimitive (Top (A := A) (X := X)) X)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card Ω - 2) ∨
      ∃ D : NonaffineData (Top (A := A) (X := X)) X, ∃ i : CFSG.Index,
        RemainingFiniteSimpleType i ∧ Nonempty (D.Simple ≃* i.Model) ∧
          ∃ K : Subgroup D.Simple, K ≠ ⊤ ∧ Nat.card X = K.index ^ D.factorCount ∧
            K.index ^ (4 * Nat.log 2 K.index + 23) <
              Nat.card D.Simple * Nat.card (Outer D.Simple) ∧
            K.index ^ 66 < Nat.card D.Simple * Nat.card (Outer D.Simple) := by
  letI : MulAction.IsPreprimitive (Top (A := A) (X := X)) X := hprimitive
  rcases PrimitiveLargeOrderFiniteResidual.card_le_or_actual_remaining_model
    hCFSG (Top (A := A) (X := X)) X hn with horder | ⟨D,i,hi,he,K,hK,hdegree,hlog,hbound⟩
  · exact Or.inl (LargeSmallFibreSubgroupClassGap.subgroup_class_cube_gap_of_top_order
      b hb c hc hsize hn horder H)
  · by_cases hf : RemainingFiniteSimpleType i
    · exact Or.inr ⟨D,i,hf,he,K,hK,hdegree,hlog,hbound⟩
    · obtain ⟨m,hm,rfl⟩ := alternating_of_remaining_not_finite i hi hf
      let e : D.Simple ≃* alternatingGroup (Fin m) := Classical.choice he
      exact Or.inl (LargeAlternatingSmallFibreSubnormalGap.subnormal_class_cube_gap
        b hb c hc hsize hn D m hm e K hK hdegree H hH)

end SymmetricSubgroupAsymptotics.LargePrimitiveIntermediateSubnormalGapResidual
