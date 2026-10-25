import SymmetricSubgroupAsymptotics.OriginalMinimalBlockComponentTransport
import SymmetricSubgroupAsymptotics.SmallTopLargePrimitiveComponentClassBound
import SymmetricSubgroupAsymptotics.GaronziMarotiLargeBlockCubeReduction

/-! An actual minimal-block choice with a large primitive component.
Arbitrary tops of degree at least four use strict-smaller GENERAL
permutation-degree induction. Tops of size two or three use the proved
primitive subnormal saving. No simultaneous primitive-top assumption
is made, and all finite-model residual data remain in the original fibre. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock
open PrimitiveSocleRawStructure LargeTopFiniteModelResidual

variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

theorem class_cube_or_actual_finite_model_of_large_component
    (hCFSG : CFSG.CFSGClassification) (hlarge : 4096 ≤ Nat.card D.Fibre)
    (hSmaller : ∀ m : ℕ, m < Nat.card Ω → 4 ≤ m →
      ∀ L : Subgroup (Equiv.Perm (Fin m)),
        Nat.card (ConjClasses L) ^ 3 ≤ 5 ^ (m - 1)) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) ∨
      ((Nat.card D.Points = 2 ∨ Nat.card D.Points = 3) ∧
        ∃ x : D.Points,
          ∃ L : Subgroup (originalBlockComponent D.map D.map_equivariant x), L.IsSubnormal ∧
            ∃ E : NonaffineData (originalBlockComponent D.map D.map_equivariant x)
                (originalBlockFibre D.map x),
              ∃ i : CFSG.Index, RemainingFiniteSimpleType i ∧ Nonempty (E.Simple ≃* i.Model) ∧
                ∃ K : Subgroup E.Simple, K ≠ ⊤ ∧ Nat.card D.Fibre = K.index ^ E.factorCount ∧
                  K.index ^ (4 * Nat.log 2 K.index + 23) <
                    Nat.card E.Simple * Nat.card (Outer E.Simple) ∧
                  K.index ^ 66 < Nat.card E.Simple * Nat.card (Outer E.Simple)) := by
  by_cases hblocks : 4 ≤ Nat.card D.Points
  · exact Or.inl
      (GaronziMarotiLargeBlockCubeReduction.exact_exponent_large_block_cube_step
        D.map D.map_equivariant (Nat.card D.Fibre) (by omega) hblocks
        D.fibre_card_at hSmaller)
  · have hsmall : Nat.card D.Points = 2 ∨ Nat.card D.Points = 3 := by
      have h := D.degrees_ge_two.2
      omega
    rcases SmallTopLargePrimitiveComponentClassBound.primitive_component_cube_or_actual_finite_model
      hCFSG D.map D.map_equivariant (Nat.card D.Fibre) hlarge hsmall
      D.fibre_card_at D.component_preprimitive_at with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hsmall,h⟩

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock
