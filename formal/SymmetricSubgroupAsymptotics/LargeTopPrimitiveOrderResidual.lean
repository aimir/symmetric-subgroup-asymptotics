import SymmetricSubgroupAsymptotics.LargeTopSmallFibreStructureBounds
import SymmetricSubgroupAsymptotics.LargeTopBoundedComponentSmallFibreClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScottProof

/-! An actual primitive top above4096 blocks is reduced to its literal
nonaffine proper-index data with TWO component-order budgets failing.
Affine and power-form tops are discharged. This is a structural residual,
not a primitive class-count or full-GM callback. No CFSG is needed here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.LargeTopPrimitiveOrderResidual
open OriginalBlockClassBound PrimitiveSocleRawStructure

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem primitive_top_cube_or_actual_index_order_failure (b : Ω → X)
    (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (c : ℕ) (hc : c = 2 ∨ c = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x) = c)
    (hn : 4096 ≤ Nat.card X)
    (hprimitive : MulAction.IsPreprimitive (Top (A := A) (X := X)) X) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) ∨
      ∃ D : NonaffineData (Top (A := A) (X := X)) X,
        ∃ K : Subgroup D.Simple, K ≠ ⊤ ∧
          Nat.card X = K.index ^ D.factorCount ∧
          K.index ^ (4 * Nat.log 2 K.index + 23) <
            Nat.card D.Simple * Nat.card (Outer D.Simple) ∧
          K.index ^ 66 < Nat.card D.Simple * Nat.card (Outer D.Simple) := by
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  letI : MulAction.IsPreprimitive (Top (A := A) (X := X)) X := hprimitive
  obtain ⟨P⟩ := publishedONanScottStructure (Top (A := A) (X := X)) X
  cases P with
  | inr P =>
    exact Or.inl (LargeTopSmallFibreStructureBounds.class_cube_le_of_affine_top
      b hb c hc hsize hn P (Classical.choice inferInstance))
  | inl D =>
    rcases D.indexForm with ⟨K,hK,hdegree⟩ | ⟨a,hka,hdegree⟩
    · by_cases hlog : Nat.card D.Simple * Nat.card (Outer D.Simple) ≤
          K.index ^ (4 * Nat.log 2 K.index + 23)
      · exact Or.inl (LargeTopSmallFibreStructureBounds.class_cube_le_of_index_top
          b hb c hc hsize hn D K hK hdegree hlog)
      · by_cases hbound : Nat.card D.Simple * Nat.card (Outer D.Simple) ≤ K.index ^ 66
        · exact Or.inl
            (LargeTopBoundedComponentSmallFibreClassBound.class_cube_le_of_bounded_component_top
              b hb c hc hsize hn D K hK hdegree hbound)
        · exact Or.inr ⟨D,K,hK,hdegree,lt_of_not_ge hlog,lt_of_not_ge hbound⟩
    · exact Or.inl (LargeTopSmallFibreStructureBounds.class_cube_le_of_power_top
        b hb c hc hsize hn D a hka hdegree)

end SymmetricSubgroupAsymptotics.LargeTopPrimitiveOrderResidual
