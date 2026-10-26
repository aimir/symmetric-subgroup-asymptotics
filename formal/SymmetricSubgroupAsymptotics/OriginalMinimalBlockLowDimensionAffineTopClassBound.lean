import SymmetricSubgroupAsymptotics.AffineTopLowDimensionSmallFibreClassBound
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockComponentTransport

/-! Same-source native installer for affine tops of translation dimension
at most three/four in their proved degree ranges. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock

variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A:=A) ω₀)

theorem subnormal_class_cube_le_of_low_dimension_affine_top
    (hc : Nat.card D.Fibre=2 ∨ Nat.card D.Fibre=3)
    (P : PrimitiveAffineProfile D.Top D.Points)
    (hd : (49 ≤ Nat.card D.Points ∧ Nat.log P.p (Nat.card D.Points) ≤ 3) ∨
      (64 ≤ Nat.card D.Points ∧ Nat.log P.p (Nat.card D.Points) ≤ 4))
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-1) :=
  AffineTopLowDimensionSmallFibreClassBound.subnormal_class_cube_le_of_affine_top_dimension
    D.map D.map_equivariant (Nat.card D.Fibre) hc D.fibre_card_at P hd H hH

theorem class_cube_le_of_low_dimension_affine_top
    (hc : Nat.card D.Fibre=2 ∨ Nat.card D.Fibre=3)
    (P : PrimitiveAffineProfile D.Top D.Points)
    (hd : (49 ≤ Nat.card D.Points ∧ Nat.log P.p (Nat.card D.Points) ≤ 3) ∨
      (64 ≤ Nat.card D.Points ∧ Nat.log P.p (Nat.card D.Points) ≤ 4)) :
    Nat.card (ConjClasses A)^3 ≤ 5^(Nat.card Ω-1) := by
  have h := D.subnormal_class_cube_le_of_low_dimension_affine_top hc P hd ⊤
    (Subgroup.Normal.isSubnormal inferInstance)
  have hc : Nat.card (ConjClasses A) ≤ Nat.card (ConjClasses (⊤ : Subgroup A)) :=
    Nat.card_le_card_of_surjective
      (ConjClasses.map (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A).toMonoidHom)
      (ConjClasses.map_surjective Subgroup.topEquiv.surjective)
  exact (Nat.pow_le_pow_left hc 3).trans h

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock
