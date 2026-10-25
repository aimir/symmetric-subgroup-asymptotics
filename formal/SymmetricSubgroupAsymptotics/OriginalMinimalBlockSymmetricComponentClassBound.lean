import SymmetricSubgroupAsymptotics.SymmetricComponentProperSubnormalClassGap
import SymmetricSubgroupAsymptotics.SmallTopProperSubnormalClassGapBound
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockComponentTransport

/-! Native original minimal-block induction for every actual component
isomorphic to S_m, m>=5. The same component and representation are kept;
only proper subnormal kernels use the extra exponent. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock

variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

theorem class_cube_le_of_symmetric_component (m : ℕ) (hm : 5 ≤ m)
    (e : D.Component ≃* Equiv.Perm (Fin m))
    (hSmaller : ∀ n : ℕ, n < Nat.card Ω → 4 ≤ n →
      ∀ L : Subgroup (Equiv.Perm (Fin n)),
        Nat.card (ConjClasses L)^3 ≤ 5^(n-1)) :
    Nat.card (ConjClasses A)^3 ≤ 5^(Nat.card Ω-1) := by
  have hdegree := SymmetricComponentDegreeLower.degree_le D.Component m (by omega) e
  have hfour : 4 ≤ Nat.card D.Fibre := by omega
  by_cases hlarge : 4 ≤ Nat.card D.Points
  · exact GaronziMarotiLargeBlockCubeReduction.exact_exponent_large_block_cube_step
      D.map D.map_equivariant (Nat.card D.Fibre) hfour hlarge D.fibre_card_at hSmaller
  have hsmall : Nat.card D.Points = 2 ∨ Nat.card D.Points = 3 := by
    have htwo := D.degrees_ge_two.2
    omega
  exact SmallTopProperSubnormalClassGapBound.class_cube_le_of_proper_subnormal_gaps
    D.map D.map_equivariant D.base (Nat.card D.Fibre) hfour rfl hsmall
    (fun L hL hne => SymmetricComponentProperSubnormalClassGap.proper_subnormal_class_cube_le
      D.Component m hm e L hL hne) hSmaller

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock
