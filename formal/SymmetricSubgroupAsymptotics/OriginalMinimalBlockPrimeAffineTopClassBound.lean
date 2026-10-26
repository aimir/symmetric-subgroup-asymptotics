import SymmetricSubgroupAsymptotics.PrimeAffineTopSmallFibreClassBound
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockComponentTransport

/-! Native prime affine top closure from its same actual profile. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock

variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A:=A) ω₀)

theorem subnormal_class_cube_le_of_prime_affine_top
    (hc : Nat.card D.Fibre=2 ∨ Nat.card D.Fibre=3)
    (hp : (Nat.card D.Points).Prime) (hn : 5 ≤ Nat.card D.Points)
    (P : PrimitiveAffineProfile D.Top D.Points)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-1) :=
  PrimeAffineTopSmallFibreClassBound.subnormal_class_cube_le_of_prime_affine_top
    D.map D.map_equivariant (Nat.card D.Fibre) hc D.fibre_card_at hp hn P H hH

theorem class_cube_le_of_prime_affine_top
    (hc : Nat.card D.Fibre=2 ∨ Nat.card D.Fibre=3)
    (hp : (Nat.card D.Points).Prime) (hn : 5 ≤ Nat.card D.Points)
    (P : PrimitiveAffineProfile D.Top D.Points) :
    Nat.card (ConjClasses A)^3 ≤ 5^(Nat.card Ω-1) := by
  have h := D.subnormal_class_cube_le_of_prime_affine_top hc hp hn P ⊤
    (Subgroup.Normal.isSubnormal inferInstance)
  have hc : Nat.card (ConjClasses A) ≤ Nat.card (ConjClasses (⊤ : Subgroup A)) :=
    Nat.card_le_card_of_surjective
      (ConjClasses.map (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A).toMonoidHom)
      (ConjClasses.map_surjective Subgroup.topEquiv.surjective)
  exact (Nat.pow_le_pow_left hc 3).trans h

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock
