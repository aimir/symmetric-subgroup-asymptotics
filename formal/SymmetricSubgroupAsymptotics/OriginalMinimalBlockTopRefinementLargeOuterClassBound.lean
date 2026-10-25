import SymmetricSubgroupAsymptotics.OriginalMinimalBlockTopRefinement
import SymmetricSubgroupAsymptotics.NestedBlockComponentAction
import SymmetricSubgroupAsymptotics.GaronziMarotiLargeBlockCubeReduction

/-! Every second minimal-block choice with at least four outer blocks
uses ordinary strict-smaller permutation induction on the composite
original block map. There is no lower cutoff on the intermediate fibre
and no primitive-top or class-count hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlockTopRefinement
open NestedBlockComponentAction

theorem class_cube_le_of_large_outer
    {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)
    (hSmaller : ∀ m : ℕ, m < Nat.card Ω → 4 ≤ m →
      ∀ L : Subgroup (Equiv.Perm (Fin m)),
        Nat.card (ConjClasses L) ^ 3 ≤ 5 ^ (m - 1)) :
    letI := D.top_pretransitive
    ∀ (E : OriginalMinimalBlock (A := D.Top) D.base), 4 ≤ Nat.card E.Points →
      Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) := by
  letI := D.top_pretransitive
  intro E hblocks
  letI := action D E
  let c := map D E
  have hc : ∀ (g : A) (x : D.Points), c (g • x) = g • c x := map_equivariant D E
  have hs : ∀ y, Nat.card (OuterFibre D.map c y) = Nat.card E.Fibre * Nat.card D.Fibre := by
    intro y
    have hf : ∀ x, Nat.card (originalBlockFibre (innerMap D.map c y) x) = Nat.card D.Fibre := by
      intro x
      exact (Nat.card_congr (innerFibreEquiv D.map c y x)).trans (D.fibre_card_at x.val)
    have h := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre
      (innerMap D.map c y) (Nat.card D.Fibre) hf
    rw [fibre_card_at D E y] at h
    exact h
  have hD := D.degrees_ge_two.1
  have hE := E.degrees_ge_two.1
  have ha : 4 ≤ Nat.card E.Fibre * Nat.card D.Fibre := by nlinarith
  exact GaronziMarotiLargeBlockCubeReduction.exact_exponent_large_block_cube_step
    (c ∘ D.map) (composite_equivariant D.map D.map_equivariant c hc)
    (Nat.card E.Fibre * Nat.card D.Fibre) ha hblocks hs hSmaller

end SymmetricSubgroupAsymptotics.OriginalMinimalBlockTopRefinement
