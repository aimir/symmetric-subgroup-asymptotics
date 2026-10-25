import SymmetricSubgroupAsymptotics.NestedBlockComponentAction
import SymmetricSubgroupAsymptotics.BlockKernelClassBound

/-! The top image for the descended action on actual inner blocks is
exactly the original component of the second map. This exposes the
literal subgroup equality used to transport primitive source data. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NestedBlockComponentTopTransport
open NestedBlockComponentAction

theorem top_eq
    {A Ω X Y : Type} [Group A] [MulAction A Ω] [MulAction A X] [MulAction A Y]
    (b : Ω → X) (hb : ∀ (g : A) (ω : Ω), b (g • ω) = g • b ω)
    (hbs : Function.Surjective b)
    (c : X → Y) (hc : ∀ (g : A) (x : X), c (g • x) = g • c x) (y : Y) :
    letI := componentAction b hb c hc hbs y
    OriginalBlockClassBound.Top (A := Component b hb c hc y) (X := InnerFibre c y) =
      originalBlockComponent c hc y := by
  letI := componentAction b hb c hc hbs y
  have ht : MulAction.toPermHom (Component b hb c hc y) (InnerFibre c y) =
      innerHom b hb c hc hbs y := by
    apply MonoidHom.ext
    intro g
    apply Equiv.ext
    intro x
    rfl
  change (MulAction.toPermHom (Component b hb c hc y) (InnerFibre c y)).range = _
  rw [ht]
  exact innerHom_range b hb c hc hbs y

end SymmetricSubgroupAsymptotics.NestedBlockComponentTopTransport
