import SymmetricSubgroupAsymptotics.PrimitiveAffineSixtyFourTopClassCapacity
import SymmetricSubgroupAsymptotics.PrimitiveTopSmallFibreClassBudget
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockComponentTransport

/-! The actual primitive affine64 top pays both original small-fibre
forms through the proved same-action unsigned reserve and its literal
subgroup capacity. No capacity or no-swap premise is supplied here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixtyFourTopSmallFibreClassBound
open OriginalBlockClassBound
open BinarySixtyFourElementSemidirectClassBound (classBudget)

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem subnormal_class_cube_le_at_original_degree
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (P : PrimitiveAffineProfile (Top (A:=A) (X:=X)) X)
    (hprimitive : MulAction.IsPreprimitive (Top (A:=A) (X:=X)) X)
    (hdegree : Nat.card X=64)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-1) := by
  letI : Nonempty X := Finite.card_pos_iff.mp (by omega)
  let x₀ : X := Classical.arbitrary X
  have horder : Nat.card (Top (A:=A) (X:=X)) < (Nat.card X).factorial :=
    (P.card_le_domain_pow_log x₀).trans_lt (by
      simpa only [hdegree] using PrimitiveAffineSixtyFourTopClassCapacity.affine_order_lt_factorial)
  have htop : ∀ L : Subgroup (Top (A:=A) (X:=X)), L.IsSubnormal →
      Nat.card (ConjClasses L) ≤ classBudget :=
    fun L _ => PrimitiveAffineSixtyFourTopClassCapacity.subgroup_class_card_le
      P hprimitive x₀ hdegree L
  exact PrimitiveTopSmallFibreClassBudget.subnormal_class_cube_le_at_original_degree
    π hπ c hc hsize (by omega) hprimitive horder classBudget
    PrimitiveAffineSixtyFourTopClassCapacity.budget_ge_eleven htop
    (by simpa only [hdegree] using PrimitiveAffineSixtyFourTopClassCapacity.binary_unsigned_capacity)
    (by simpa only [hdegree] using PrimitiveAffineSixtyFourTopClassCapacity.ternary_capacity) H hH

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixtyFourTopSmallFibreClassBound

namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock

variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A:=A) ω₀)

theorem subnormal_class_cube_le_of_primitive_sixtyFour_affine_top
    (hc : Nat.card D.Fibre=2 ∨ Nat.card D.Fibre=3)
    (P : PrimitiveAffineProfile D.Top D.Points)
    (hprimitive : MulAction.IsPreprimitive D.Top D.Points)
    (hdegree : Nat.card D.Points=64)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-1) :=
  PrimitiveAffineSixtyFourTopSmallFibreClassBound.subnormal_class_cube_le_at_original_degree
    D.map D.map_equivariant (Nat.card D.Fibre) hc D.fibre_card_at P hprimitive hdegree H hH

theorem class_cube_le_of_primitive_sixtyFour_affine_top
    (hc : Nat.card D.Fibre=2 ∨ Nat.card D.Fibre=3)
    (P : PrimitiveAffineProfile D.Top D.Points)
    (hprimitive : MulAction.IsPreprimitive D.Top D.Points)
    (hdegree : Nat.card D.Points=64) :
    Nat.card (ConjClasses A)^3 ≤ 5^(Nat.card Ω-1) := by
  have h := D.subnormal_class_cube_le_of_primitive_sixtyFour_affine_top hc P hprimitive hdegree ⊤
    (Subgroup.Normal.isSubnormal inferInstance)
  have hc : Nat.card (ConjClasses A) ≤ Nat.card (ConjClasses (⊤ : Subgroup A)) :=
    Nat.card_le_card_of_surjective
      (ConjClasses.map (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A).toMonoidHom)
      (ConjClasses.map_surjective Subgroup.topEquiv.surjective)
  exact (Nat.pow_le_pow_left hc 3).trans h

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock
