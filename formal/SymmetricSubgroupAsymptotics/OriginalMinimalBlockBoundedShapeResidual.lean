import SymmetricSubgroupAsymptotics.OriginalMinimalBlockLargeComponentClassBound
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockFourComponentClassBound
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockLargeTopRefinementClassResidual
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockTopRefinementLargeOuterClassBound

/-! Exhaustion of an actual minimal block choice. Every unbounded branch
uses a proved induction step or retains literal Tits/sporadic data in the
same original component or faithful top. The bounded alternative is a
shape bound only; no class bound at bounded degree is assumed here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlockBoundedShapeResidual
open PrimitiveSocleRawStructure LargeTopFiniteModelResidual

variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

def ComponentResidual : Prop :=
  (Nat.card D.Points = 2 ∨ Nat.card D.Points = 3) ∧
    ∃ x : D.Points,
      ∃ L : Subgroup (originalBlockComponent D.map D.map_equivariant x), L.IsSubnormal ∧
        ∃ E : NonaffineData (originalBlockComponent D.map D.map_equivariant x)
            (originalBlockFibre D.map x),
          ∃ i : CFSG.Index, RemainingFiniteSimpleType i ∧ Nonempty (E.Simple ≃* i.Model) ∧
            ∃ K : Subgroup E.Simple, K ≠ ⊤ ∧ Nat.card D.Fibre = K.index ^ E.factorCount ∧
              K.index ^ (4 * Nat.log 2 K.index + 23) <
                Nat.card E.Simple * Nat.card (Outer E.Simple) ∧
              K.index ^ 66 < Nat.card E.Simple * Nat.card (Outer E.Simple)

def TopResidual : Prop :=
  ∃ E : NonaffineData D.Top D.Points,
    ∃ i : CFSG.Index, RemainingFiniteSimpleType i ∧ Nonempty (E.Simple ≃* i.Model) ∧
      ∃ K : Subgroup E.Simple, K ≠ ⊤ ∧ Nat.card D.Points = K.index ^ E.factorCount ∧
        K.index ^ (4 * Nat.log 2 K.index + 23) <
          Nat.card E.Simple * Nat.card (Outer E.Simple) ∧
        K.index ^ 66 < Nat.card E.Simple * Nat.card (Outer E.Simple)

def RefinementResidual : Prop :=
  letI := D.top_pretransitive
  ∃ E : OriginalMinimalBlock (A := D.Top) D.base,
    letI := OriginalMinimalBlockTopRefinement.action D E
    (Nat.card E.Points = 2 ∨ Nat.card E.Points = 3) ∧
      ∃ y : E.Points,
        ∃ L : Subgroup (NestedBlockComponentAction.Component D.map D.map_equivariant
          (OriginalMinimalBlockTopRefinement.map D E)
          (OriginalMinimalBlockTopRefinement.map_equivariant D E) y),
        L.IsSubnormal ∧
          5 ^ (Nat.card E.Fibre * Nat.card D.Fibre - 2) < Nat.card (ConjClasses L) ^ 3 ∧
          ∃ F : NonaffineData
              (originalBlockComponent (A := A) (OriginalMinimalBlockTopRefinement.map D E)
                (OriginalMinimalBlockTopRefinement.map_equivariant D E) y)
              (originalBlockFibre (OriginalMinimalBlockTopRefinement.map D E) y),
            ∃ i : CFSG.Index, RemainingFiniteSimpleType i ∧ Nonempty (F.Simple ≃* i.Model) ∧
              ∃ K : Subgroup F.Simple, K ≠ ⊤ ∧ Nat.card E.Fibre = K.index ^ F.factorCount ∧
                K.index ^ (4 * Nat.log 2 K.index + 23) <
                  Nat.card F.Simple * Nat.card (Outer F.Simple) ∧
                K.index ^ 66 < Nat.card F.Simple * Nat.card (Outer F.Simple)

def ActualFiniteModelResidual : Prop :=
  ComponentResidual D ∨ TopResidual D ∨ RefinementResidual D

theorem class_cube_or_bounded_shape_or_actual_finite_model
    (hCFSG : CFSG.CFSGClassification)
    (hSmaller : ∀ m : ℕ, m < Nat.card Ω → 4 ≤ m →
      ∀ L : Subgroup (Equiv.Perm (Fin m)),
        Nat.card (ConjClasses L) ^ 3 ≤ 5 ^ (m - 1)) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) ∨
      Nat.card Ω ≤ 36855 ∨ ActualFiniteModelResidual D := by
  have hD := D.degrees_ge_two
  have hprod := D.degree_product
  by_cases hfour : Nat.card D.Fibre = 4
  · exact Or.inl (D.class_cube_le_of_four_point_component hfour hSmaller)
  by_cases ha : 4 ≤ Nat.card D.Fibre
  · by_cases hb : 4 ≤ Nat.card D.Points
    · exact Or.inl
        (GaronziMarotiLargeBlockCubeReduction.exact_exponent_large_block_cube_step
          D.map D.map_equivariant (Nat.card D.Fibre) ha hb D.fibre_card_at hSmaller)
    · by_cases hlarge : 4096 ≤ Nat.card D.Fibre
      · rcases D.class_cube_or_actual_finite_model_of_large_component hCFSG hlarge hSmaller with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
      · have hbound := Nat.mul_le_mul
          (show Nat.card D.Fibre ≤ 4095 by omega)
          (show Nat.card D.Points ≤ 3 by omega)
        exact Or.inr (Or.inl (by omega))
  · have hsmall : Nat.card D.Fibre = 2 ∨ Nat.card D.Fibre = 3 := by omega
    letI := D.top_pretransitive
    letI : Finite D.Top := D.top_finite
    letI : Nontrivial D.Points := Finite.one_lt_card_iff_nontrivial.mp hD.2
    by_cases hp : MulAction.IsPreprimitive D.Top D.Points
    · by_cases hlarge : 4096 ≤ Nat.card D.Points
      · rcases LargeTopFiniteModelResidual.primitive_top_cube_or_actual_finite_model
          hCFSG D.map D.map_equivariant (Nat.card D.Fibre) hsmall D.fibre_card_at
          hlarge hp with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · have hbound := Nat.mul_le_mul
          (show Nat.card D.Fibre ≤ 3 by omega)
          (show Nat.card D.Points ≤ 4095 by omega)
        exact Or.inr (Or.inl (by omega))
    · obtain ⟨E⟩ := originalMinimalBlock_nonempty D.base hp
      have hE := E.degrees_ge_two
      have hEprod := E.degree_product
      by_cases houter : 4 ≤ Nat.card E.Points
      · exact Or.inl
          (OriginalMinimalBlockTopRefinement.class_cube_le_of_large_outer D hSmaller E houter)
      · by_cases hlarge : 4096 ≤ Nat.card E.Fibre
        · rcases D.class_cube_or_actual_finite_model_of_large_top_refinement
            hCFSG hsmall hSmaller E hlarge with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨E,h⟩)))
        · have hboundE := Nat.mul_le_mul
            (show Nat.card E.Fibre ≤ 4095 by omega)
            (show Nat.card E.Points ≤ 3 by omega)
          have hb : Nat.card D.Points ≤ 12285 := by omega
          have hbound := Nat.mul_le_mul (show Nat.card D.Fibre ≤ 3 by omega) hb
          exact Or.inr (Or.inl (by omega))

end SymmetricSubgroupAsymptotics.OriginalMinimalBlockBoundedShapeResidual
