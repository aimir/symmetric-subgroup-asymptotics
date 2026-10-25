import SymmetricSubgroupAsymptotics.PrimitiveSocleExceptionalEProperSubnormalClassGap
import SymmetricSubgroupAsymptotics.SmallTopProperSubnormalClassGapBound
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockComponentTransport

/-! The native original-action induction step for the whole E6/E7/E8
component family. The model alternatives are actual group equivalences,
and every class/outer/index budget is discharged by its proved packet. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock
open PrimitiveSocleRawStructure

variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

theorem class_cube_le_of_exceptionalE_component
    (E : NonaffineData D.Component D.Fibre)
    (hmodel : (∃ q : CFSG.PrimePower, Nonempty (E.Simple ≃* CFSG.Models.E6 q)) ∨
      (∃ q : CFSG.PrimePower, Nonempty (E.Simple ≃* CFSG.Models.E7 q)) ∨
      (∃ q : CFSG.PrimePower, Nonempty (E.Simple ≃* CFSG.Models.E8 q)))
    (hdegree : 4 ≤ Nat.card D.Fibre)
    (hSmaller : ∀ n : ℕ, n < Nat.card Ω → 4 ≤ n →
      ∀ L : Subgroup (Equiv.Perm (Fin n)),
        Nat.card (ConjClasses L)^3 ≤ 5^(n-1)) :
    Nat.card (ConjClasses A)^3 ≤ 5^(Nat.card Ω-1) := by
  by_cases hlarge : 4 ≤ Nat.card D.Points
  · exact GaronziMarotiLargeBlockCubeReduction.exact_exponent_large_block_cube_step
      D.map D.map_equivariant (Nat.card D.Fibre) hdegree hlarge D.fibre_card_at hSmaller
  have hsmall : Nat.card D.Points = 2 ∨ Nat.card D.Points = 3 := by
    have htwo := D.degrees_ge_two.2
    omega
  apply SmallTopProperSubnormalClassGapBound.class_cube_le_of_proper_subnormal_gaps
    D.map D.map_equivariant D.base (Nat.card D.Fibre) hdegree rfl hsmall _ hSmaller
  intro L hL hne
  rcases hmodel with ⟨q, ⟨e⟩⟩ | ⟨q, ⟨e⟩⟩ | ⟨q, ⟨e⟩⟩
  · exact E.proper_subnormal_class_cube_le_of_typeE6 q e (by omega) L hL hne
  · exact E.proper_subnormal_class_cube_le_of_typeE7 q e (by omega) L hL hne
  · exact E.proper_subnormal_class_cube_le_of_typeE8 q e (by omega) L hL hne

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock
