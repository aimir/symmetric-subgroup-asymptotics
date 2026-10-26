import SymmetricSubgroupAsymptotics.CFSGMathieuElevenActualClassCount
import SymmetricSubgroupAsymptotics.CFSGMathieuElevenMinimumIndex
import SymmetricSubgroupAsymptotics.PrimitiveSocleClassCubeSquareProperGap
import SymmetricSubgroupAsymptotics.FiniteSimpleModelSmallFibreClassConsumer
import SymmetricSubgroupAsymptotics.SmallTopProperSubnormalClassGapBound
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockComponentTransport

/-! CONDITIONAL consumers of a raw M11 outer-cardinal bound. All actual
class/order/index metadata are supplied internally, but the outer bound
is NOT proved here or installed as an endpoint assumption. Original
socle data, subnormal sources, block systems and both degree forms remain
literal; no existing exhaustive profile is edited. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuElevenClassConsumersOfOuterOne
open PrimitiveSocleRawStructure CFSG.Models.Presentations.M11

private theorem component_cube [IsSimpleGroup Model]
    (houter : Nat.card (Outer Model) ≤ 1) :
    (Nat.card (ConjClasses Model) * Nat.card (Outer Model)) ^ 3 ≤ 5 ^ (11 - 1) := by
  exact (Nat.pow_le_pow_left
    (Nat.mul_le_mul CFSGMathieuElevenActualClassCount.class_card_le_ten houter) 3).trans
      (by norm_num)

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem primitive_subnormal_class_cube (D : NonaffineData G X)
    (e : D.Simple ≃* Model) (houter : Nat.card (Outer Model) ≤ 1)
    (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 1) := by
  letI : Finite Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup Model := e.symm.isSimpleGroup
  apply D.subnormal_class_cube_le_of_model_capacity Model e 11 (by decide)
    CFSGMathieuElevenMinimumIndex.proper_index_ge_eleven (component_cube houter) ?_ H hH
  rw [CFSGMathieuElevenActualEquivalence.card]
  decide

theorem proper_subnormal_class_cube_gap (D : NonaffineData G X)
    (e : D.Simple ≃* Model) (houter : Nat.card (Outer Model) ≤ 1)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 2) := by
  letI : Finite Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup Model := e.symm.isSimpleGroup
  apply D.proper_subnormal_class_cube_le_of_model_square_capacity Model e 11 (by decide)
    CFSGMathieuElevenMinimumIndex.proper_index_ge_eleven (component_cube houter) ?_ H hH hne
  rw [CFSGMathieuElevenActualEquivalence.card]
  decide

theorem original_small_fibre_subnormal_gap
    {A Ω Y : Type} [Group A] [MulAction A Ω] [MulAction A Y]
    [Finite A] [Finite Ω] [Finite Y] [FaithfulSMul A Ω]
    (π : Ω → Y) (hπ : ∀ (g : A) (ω : Ω), π (g • ω) = g • π ω)
    (c : ℕ) (hc : c = 2 ∨ c = 3)
    (hsize : ∀ y, Nat.card (originalBlockFibre π y) = c)
    (E : NonaffineData (OriginalBlockClassBound.Top (A := A) (X := Y)) Y)
    (e : E.Simple ≃* Model) (houter : Nat.card (Outer Model) ≤ 1)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card Ω - 2) := by
  letI : Finite Model := Finite.of_equiv E.Simple e.toEquiv
  letI : IsSimpleGroup Model := e.symm.isSimpleGroup
  exact FiniteSimpleModelSmallFibreClassConsumer.subnormal_class_cube_gap_of_model_bounds
    π hπ c hc hsize E Model e 11 10 1 CFSGMathieuElevenMinimumIndex.proper_index_ge_eleven
    CFSGMathieuElevenActualClassCount.class_card_le_ten houter (by norm_num)
    CFSGMathieuElevenActualIndexSquare.index_square H hH

theorem original_component_class_cube
    {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)
    (E : NonaffineData D.Component D.Fibre) (e : E.Simple ≃* Model)
    (houter : Nat.card (Outer Model) ≤ 1) (hdegree : 4 ≤ Nat.card D.Fibre)
    (hSmaller : ∀ n : ℕ, n < Nat.card Ω → 4 ≤ n →
      ∀ L : Subgroup (Equiv.Perm (Fin n)),
        Nat.card (ConjClasses L) ^ 3 ≤ 5 ^ (n - 1)) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) := by
  by_cases hlarge : 4 ≤ Nat.card D.Points
  · exact GaronziMarotiLargeBlockCubeReduction.exact_exponent_large_block_cube_step
      D.map D.map_equivariant (Nat.card D.Fibre) hdegree hlarge D.fibre_card_at hSmaller
  have hsmall : Nat.card D.Points = 2 ∨ Nat.card D.Points = 3 := by
    have htwo := D.degrees_ge_two.2
    omega
  exact SmallTopProperSubnormalClassGapBound.class_cube_le_of_proper_subnormal_gaps
    D.map D.map_equivariant D.base (Nat.card D.Fibre) hdegree rfl hsmall
    (fun L hL hne => proper_subnormal_class_cube_gap E e houter L hL hne) hSmaller

end SymmetricSubgroupAsymptotics.CFSGMathieuElevenClassConsumersOfOuterOne
