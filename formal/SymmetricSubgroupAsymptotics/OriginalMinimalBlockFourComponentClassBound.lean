import SymmetricSubgroupAsymptotics.OriginalMinimalBlockComponentTransport
import SymmetricSubgroupAsymptotics.SmallTopPrimitiveFourClassBound
import SymmetricSubgroupAsymptotics.GaronziMarotiLargeBlockCubeReduction

/-! The original minimal-block induction step for a four-point fibre.
Large tops use strict-smaller general permutation induction; literal
two- and three-point tops use the proved proper/full-base dichotomy.
Only the component is primitive, with no primitive-top assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock

variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

theorem class_cube_le_of_four_point_component (hfour : Nat.card D.Fibre = 4)
    (hSmaller : ∀ m : ℕ, m < Nat.card Ω → 4 ≤ m →
      ∀ L : Subgroup (Equiv.Perm (Fin m)),
        Nat.card (ConjClasses L) ^ 3 ≤ 5 ^ (m - 1)) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) := by
  by_cases hblocks : 4 ≤ Nat.card D.Points
  · exact GaronziMarotiLargeBlockCubeReduction.exact_exponent_large_block_cube_step
      D.map D.map_equivariant 4 (by decide) hblocks
      (fun x => (D.fibre_card_at x).trans hfour) hSmaller
  · have hsmall : Nat.card D.Points = 2 ∨ Nat.card D.Points = 3 := by
      have h := D.degrees_ge_two.2
      omega
    exact SmallTopPrimitiveFourClassBound.class_cube_le
      D.map D.map_equivariant D.base hsmall D.component_preprimitive hfour

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock
