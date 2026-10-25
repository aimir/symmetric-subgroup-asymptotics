import SymmetricSubgroupAsymptotics.OriginalMinimalBlockTopRefinement
import SymmetricSubgroupAsymptotics.NestedBlockPrimitiveIntermediateClassResidual
import SymmetricSubgroupAsymptotics.GaronziMarotiLargeBlockCubeReduction

/-! Two successive actual minimal-block choices in the original action.
A large second fibre gives the GM cube, except for literal Tits/sporadic
data in the original intermediate component. The intermediate primitivity
is proved by the second cover and surjective-source transport. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock
open NestedBlockComponentAction PrimitiveSocleRawStructure LargeTopFiniteModelResidual

theorem class_cube_or_actual_finite_model_of_large_top_refinement
    (hCFSG : CFSG.CFSGClassification)
    {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)
    (hsmall : Nat.card D.Fibre = 2 ∨ Nat.card D.Fibre = 3)
    (hSmaller : ∀ m : ℕ, m < Nat.card Ω → 4 ≤ m →
      ∀ L : Subgroup (Equiv.Perm (Fin m)),
        Nat.card (ConjClasses L) ^ 3 ≤ 5 ^ (m - 1)) :
    letI := D.top_pretransitive
    ∀ (E : OriginalMinimalBlock (A := D.Top) D.base), 4096 ≤ Nat.card E.Fibre →
    letI := OriginalMinimalBlockTopRefinement.action D E
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) ∨
      ((Nat.card E.Points = 2 ∨ Nat.card E.Points = 3) ∧
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
                  K.index ^ 66 < Nat.card F.Simple * Nat.card (Outer F.Simple)) := by
  letI := D.top_pretransitive
  intro E hlarge
  letI := OriginalMinimalBlockTopRefinement.action D E
  let c := OriginalMinimalBlockTopRefinement.map D E
  have hc : ∀ (g : A) (x : D.Points), c (g • x) = g • c x :=
    OriginalMinimalBlockTopRefinement.map_equivariant D E
  have hs : ∀ y, Nat.card (OuterFibre D.map c y) = Nat.card E.Fibre * Nat.card D.Fibre := by
    intro y
    have hf : ∀ x, Nat.card (originalBlockFibre (innerMap D.map c y) x) = Nat.card D.Fibre := by
      intro x
      exact (Nat.card_congr (innerFibreEquiv D.map c y x)).trans (D.fibre_card_at x.val)
    have h := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre
      (innerMap D.map c y) (Nat.card D.Fibre) hf
    rw [OriginalMinimalBlockTopRefinement.fibre_card_at D E y] at h
    exact h
  by_cases hblocks : 4 ≤ Nat.card E.Points
  · have hk := D.degrees_ge_two.1
    have ha : 4 ≤ Nat.card E.Fibre * Nat.card D.Fibre := by nlinarith
    exact Or.inl
      (GaronziMarotiLargeBlockCubeReduction.exact_exponent_large_block_cube_step
        (c ∘ D.map) (composite_equivariant D.map D.map_equivariant c hc)
        (Nat.card E.Fibre * Nat.card D.Fibre) ha hblocks hs hSmaller)
  · have hsmallTop : Nat.card E.Points = 2 ∨ Nat.card E.Points = 3 := by
      have h := E.degrees_ge_two.2
      omega
    rcases NestedBlockPrimitiveIntermediateClassResidual.class_cube_or_actual_finite_model
      hCFSG D.map D.map_equivariant D.map_surjective c hc
      (Nat.card D.Fibre) hsmall D.fibre_card_at (Nat.card E.Fibre) hlarge
      (OriginalMinimalBlockTopRefinement.fibre_card_at D E) hsmallTop
      (OriginalMinimalBlockTopRefinement.component_preprimitive_at D E) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hsmallTop,h⟩

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock
