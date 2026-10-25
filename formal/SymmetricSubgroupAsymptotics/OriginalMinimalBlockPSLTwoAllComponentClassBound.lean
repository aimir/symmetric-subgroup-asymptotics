import SymmetricSubgroupAsymptotics.PrimitiveSoclePSLTwoAllProperSubnormalClassGap
import SymmetricSubgroupAsymptotics.SmallTopProperSubnormalClassGapBound
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockComponentTransport

/-! Every original PSL2 simple-socle component pays the native GM
induction step in every representation and at every socle factor count. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock
open PrimitiveSocleRawStructure
variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

theorem class_cube_le_of_pslTwo_component
    (E : NonaffineData D.Component D.Fibre) (q : CFSG.PrimePower) (hq : 4 ≤ q.order)
    (e : E.Simple ≃* CFSG.Models.A 1 q) (hdegree : 4 ≤ Nat.card D.Fibre)
    (hSmaller : ∀ n : ℕ, n < Nat.card Ω → 4 ≤ n →
      ∀ L : Subgroup (Equiv.Perm (Fin n)),
        Nat.card (ConjClasses L)^3 ≤ 5^(n-1)) :
    Nat.card (ConjClasses A)^3 ≤ 5^(Nat.card Ω-1) := by
  by_cases hlarge : 4 ≤ Nat.card D.Points
  · exact GaronziMarotiLargeBlockCubeReduction.exact_exponent_large_block_cube_step
      D.map D.map_equivariant (Nat.card D.Fibre) hdegree hlarge D.fibre_card_at hSmaller
  have hsmall : Nat.card D.Points=2 ∨ Nat.card D.Points=3 := by
    have htwo := D.degrees_ge_two.2
    omega
  exact SmallTopProperSubnormalClassGapBound.class_cube_le_of_proper_subnormal_gaps
    D.map D.map_equivariant D.base (Nat.card D.Fibre) hdegree rfl hsmall
    (fun L hL hne => E.proper_subnormal_class_cube_le_of_pslTwo_all_fields
      q hq e L hL hne) hSmaller

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock
