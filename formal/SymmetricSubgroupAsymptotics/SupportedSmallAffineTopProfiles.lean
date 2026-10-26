import SymmetricSubgroupAsymptotics.RegularAffineFrattiniTopSmallFibreClassBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineBinaryTopSmallFibreClassBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineNineTopSmallFibreClassBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineTwentyFiveTopSmallFibreClassBound

/-! Exact small affine-top profiles with genuine native consumers.
Bare regular normal prime-group profiles suffice in every listed case
except ternary fibres above degree eight, where the existing primitive
module chart remains explicitly required. The actual H and block map
are retained in every branch; no numerical budget is a premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock

variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A:=A) ω₀)

def HasSupportedSmallAffineTop : Prop :=
  ∃ P : PrimitiveAffineProfile D.Top D.Points,
    (Nat.card D.Points=16 ∨ Nat.card D.Points=27 ∨ Nat.card D.Points=32 ∨
      Nat.card D.Points=64 ∨ (Nat.card D.Points=8 ∧ Nat.card D.Fibre=2)) ∨
    (Nat.card D.Points=8 ∧ MulAction.IsPreprimitive D.Top D.Points) ∨
    Nat.card D.Points=9 ∨ Nat.card D.Points=25

theorem subnormal_class_cube_le_of_supported_small_affine_top
    (hc : Nat.card D.Fibre=2 ∨ Nat.card D.Fibre=3)
    (h : D.HasSupportedSmallAffineTop) (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-1) := by
  rcases h with ⟨P,hselected|⟨h8,hprimitive⟩|h9|h25⟩
  · exact RegularAffineFrattiniTopSmallFibreClassBound.subnormal_class_cube_le_at_original_degree
      D.map D.map_equivariant (Nat.card D.Fibre) hc D.fibre_card_at P hselected H hH
  · exact D.subnormal_class_cube_le_of_primitive_binary_affine_top hc P hprimitive
      (Or.inl h8) H hH
  · exact D.subnormal_class_cube_le_of_primitive_nine_affine_top hc P h9 H hH
  · exact D.subnormal_class_cube_le_of_primitive_twentyFive_affine_top hc P h25 H hH

theorem class_cube_le_of_supported_small_affine_top
    (hc : Nat.card D.Fibre=2 ∨ Nat.card D.Fibre=3)
    (h : D.HasSupportedSmallAffineTop) :
    Nat.card (ConjClasses A)^3≤5^(Nat.card Ω-1) := by
  have hh := D.subnormal_class_cube_le_of_supported_small_affine_top hc h ⊤
    (Subgroup.Normal.isSubnormal inferInstance)
  have he := conjugacyClass_card_congr
    (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A)
  rwa [he] at hh

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock
