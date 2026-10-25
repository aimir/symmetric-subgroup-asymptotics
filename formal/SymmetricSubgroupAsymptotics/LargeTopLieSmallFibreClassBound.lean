import SymmetricSubgroupAsymptotics.LargeTopPrimitiveOrderResidual
import SymmetricSubgroupAsymptotics.CFSGModelComponentIndexOrderBudget

/-! Actual binary and ternary block actions with a primitive top on at
least4096 blocks. Every Lie-type top is discharged by the proved order
budgets on its SAME simple factor and proper-index subgroup. The only
remaining literal factor tags are alternating, Tits and sporadic; no
class-count hypothesis on any model is introduced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.LargeTopLieSmallFibreClassBound
open OriginalBlockClassBound PrimitiveSocleRawStructure
open CFSGModelComponentIndexOrderBudget

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem class_cube_le_of_lie_index_top
    (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x)=c)
    (hn : 4096 ≤ Nat.card X)
    (D : NonaffineData (Top (A := A) (X := X)) X)
    (K : Subgroup D.Simple) (hK : K≠⊤)
    (hdegree : Nat.card X=K.index^D.factorCount)
    (i : CFSG.Index) (hi : ¬RemainingSimpleType i) (e : D.Simple ≃* i.Model) :
    Nat.card (ConjClasses A)^3 ≤ 5^(Nat.card Ω-1) := by
  letI : Finite i.Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup i.Model := e.symm.isSimpleGroup
  have hn' : ¬IsMulCommutative i.Model :=
    fun h => D.noncommutative ((CFSGReduction.isMulCommutative_congr e).mpr h)
  have hmodel : ComponentIndexOrderBudget i.Model :=
    (model_budget_or_remaining i hn').resolve_right hi
  rcases budget_of_mulEquiv e hmodel K hK with hlog | hbound
  · exact LargeTopSmallFibreStructureBounds.class_cube_le_of_index_top
      b hb c hc hsize hn D K hK hdegree hlog
  · exact LargeTopBoundedComponentSmallFibreClassBound.class_cube_le_of_bounded_component_top
      b hb c hc hsize hn D K hK hdegree hbound

theorem primitive_top_cube_or_actual_remaining_model
    (hCFSG : CFSG.CFSGClassification)
    (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x)=c)
    (hn : 4096 ≤ Nat.card X)
    (hprimitive : MulAction.IsPreprimitive (Top (A := A) (X := X)) X) :
    Nat.card (ConjClasses A)^3 ≤ 5^(Nat.card Ω-1) ∨
      ∃ D : NonaffineData (Top (A := A) (X := X)) X,
        ∃ i : CFSG.Index, RemainingSimpleType i ∧ Nonempty (D.Simple ≃* i.Model) ∧
          ∃ K : Subgroup D.Simple, K≠⊤ ∧ Nat.card X=K.index^D.factorCount ∧
            K.index^(4*Nat.log 2 K.index+23) < Nat.card D.Simple*Nat.card (Outer D.Simple) ∧
            K.index^66 < Nat.card D.Simple*Nat.card (Outer D.Simple) := by
  rcases LargeTopPrimitiveOrderResidual.primitive_top_cube_or_actual_index_order_failure
    b hb c hc hsize hn hprimitive with h | ⟨D,K,hK,hdegree,hlog,hbound⟩
  · exact Or.inl h
  · rcases simple_budget_or_actual_remaining_model hCFSG D.Simple D.noncommutative with h | h
    · rcases h K hK with h | h
      · exact (not_lt_of_ge h hlog).elim
      · exact (not_lt_of_ge h hbound).elim
    · obtain ⟨i,hi,he⟩ := h
      exact Or.inr ⟨D,i,hi,he,K,hK,hdegree,hlog,hbound⟩

end SymmetricSubgroupAsymptotics.LargeTopLieSmallFibreClassBound
