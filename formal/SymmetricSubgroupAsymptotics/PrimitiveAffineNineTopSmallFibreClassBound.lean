import SymmetricSubgroupAsymptotics.PrimitiveTopSmallFibreClassBudget
import SymmetricSubgroupAsymptotics.AffineDegreeNineSubgroupClassGap
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockComponentTransport

/-! The already proved actual affine-nine class bound pays binary and
ternary fibres through the common native motion-reserve consumer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineNineTopSmallFibreClassBound
open OriginalBlockClassBound

theorem subnormal_class_cube_le_at_original_degree
    {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω) = g • π ω)
    (c : ℕ) (hc : c = 2 ∨ c = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x) = c)
    (P : PrimitiveAffineProfile (Top (A := A) (X := X)) X)
    (hdegree : Nat.card X = 9)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) := by
  letI : Nonempty X := Finite.card_pos_iff.mp (by omega)
  let x : X := Classical.arbitrary X
  apply PrimitiveTopSmallFibreClassBudget.subnormal_class_cube_le_of_regular_top
    π hπ c hc hsize P (by omega) 39 (by decide) ?_ ?_ ?_ H hH
  · intro L _
    exact AffineDegreeNineSubgroupClassGap.subgroup_class_card_le_thirtyNine P x hdegree L
  · rw [hdegree]
    decide +kernel
  · rw [hdegree]
    decide +kernel

end SymmetricSubgroupAsymptotics.PrimitiveAffineNineTopSmallFibreClassBound

namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock
variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

theorem subnormal_class_cube_le_of_primitive_nine_affine_top
    (hc : Nat.card D.Fibre = 2 ∨ Nat.card D.Fibre = 3)
    (P : PrimitiveAffineProfile D.Top D.Points)
    (hdegree : Nat.card D.Points = 9)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) :=
  PrimitiveAffineNineTopSmallFibreClassBound.subnormal_class_cube_le_at_original_degree
    D.map D.map_equivariant (Nat.card D.Fibre) hc D.fibre_card_at P hdegree H hH

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock
