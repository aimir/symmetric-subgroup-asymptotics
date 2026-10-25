import SymmetricSubgroupAsymptotics.OriginalMinimalBlockAffineComponentClassGap
import SymmetricSubgroupAsymptotics.GaronziMarotiLargeBlockCubeReduction

/-! Native induction for an original minimal block with one actual affine
base profile and fibre degree at least five. Two/three blocks use the
proved stronger affine gap; every larger literal top uses only the
strict-smaller general permutation-degree induction hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock

variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

theorem class_cube_le_of_affine_component
    (P : PrimitiveAffineProfile D.Component D.Fibre)
    (hdegree : 5 ≤ Nat.card D.Fibre)
    (hSmaller : ∀ m : ℕ, m < Nat.card Ω → 4 ≤ m →
      ∀ L : Subgroup (Equiv.Perm (Fin m)),
        Nat.card (ConjClasses L) ^ 3 ≤ 5 ^ (m - 1)) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) := by
  by_cases hlarge : 4 ≤ Nat.card D.Points
  · exact GaronziMarotiLargeBlockCubeReduction.exact_exponent_large_block_cube_step
      D.map D.map_equivariant (Nat.card D.Fibre) (by omega) hlarge D.fibre_card_at hSmaller
  have hsmall : Nat.card D.Points = 2 ∨ Nat.card D.Points = 3 := by
    have htwo := D.degrees_ge_two.2
    omega
  exact D.class_cube_le_of_affine_small_top P hsmall hdegree

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock
