import SymmetricSubgroupAsymptotics.SmallTopGaronziMarotiCubes
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockComponentTransport

/-! Arbitrary-carrier native use of the already-proved two/three-block
fusion bounds. Only the top labels are transported: the original group,
original point set and equal physical fibres are retained. This theorem
is for the original transitive source, not an assertion that every
subnormal subgroup remains transitive on the blocks. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OriginalSmallTopClassCubeBound

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [MulAction.IsPretransitive A X] [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

private theorem class_cube_le_after_relabel
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (n : ℕ) (e : X ≃ Fin n) (hn : n=2 ∨ n=3) :
    Nat.card (ConjClasses A)^3 ≤ 5^(Nat.card Ω-1) := by
  let f : A →* Equiv.Perm (Fin n) := e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom A X)
  letI : MulAction A (Fin n) := MulAction.compHom (Fin n) f
  letI : MulAction.IsPretransitive A (Fin n) := ⟨fun i j => by
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq A (e.symm i) (e.symm j)
    refine ⟨g,?_⟩
    change e (g • e.symm i)=j
    rw [hg,e.apply_symm_apply]⟩
  let b : Ω → Fin n := fun ω => e (π ω)
  have hb : ∀ (g : A) (ω : Ω), b (g • ω)=g • b ω := by
    intro g ω
    change e (π (g • ω))=e (g • e.symm (e (π ω)))
    rw [hπ,e.symm_apply_apply]
  have hfibre (i : Fin n) : Nat.card (originalBlockFibre b i)=c := by
    let a : originalBlockFibre b i ≃ originalBlockFibre π (e.symm i) := {
      toFun := fun ω => ⟨ω.val,e.injective
        (ω.property.trans (e.apply_symm_apply i).symm)⟩
      invFun := fun ω => ⟨ω.val,(congrArg e ω.property).trans (e.apply_symm_apply i)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    exact (Nat.card_congr a).trans (hsize (e.symm i))
  rcases hn with rfl|rfl <;> rcases hc with rfl|rfl
  · exact SmallTopGaronziMarotiCubes.binary_two_blocks_cube b hb hfibre
  · exact SmallTopGaronziMarotiCubes.ternary_two_blocks_cube b hb hfibre
  · exact SmallTopGaronziMarotiCubes.binary_three_blocks_cube b hb hfibre
  · exact SmallTopGaronziMarotiCubes.ternary_three_blocks_cube b hb hfibre

theorem class_cube_le_of_two_or_three_blocks
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (hn : Nat.card X=2 ∨ Nat.card X=3) :
    Nat.card (ConjClasses A)^3 ≤ 5^(Nat.card Ω-1) :=
  class_cube_le_after_relabel π hπ c hc hsize (Nat.card X)
    (Finite.equivFinOfCardEq rfl) hn

end SymmetricSubgroupAsymptotics.OriginalSmallTopClassCubeBound

namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock

variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A:=A) ω₀)

theorem class_cube_le_of_two_or_three_blocks
    (hc : Nat.card D.Fibre=2 ∨ Nat.card D.Fibre=3)
    (hn : Nat.card D.Points=2 ∨ Nat.card D.Points=3) :
    Nat.card (ConjClasses A)^3 ≤ 5^(Nat.card Ω-1) :=
  OriginalSmallTopClassCubeBound.class_cube_le_of_two_or_three_blocks
    D.map D.map_equivariant (Nat.card D.Fibre) hc D.fibre_card_at hn

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock
