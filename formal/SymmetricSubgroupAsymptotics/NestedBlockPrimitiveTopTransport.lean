import SymmetricSubgroupAsymptotics.NestedBlockComponentTopTransport
import Mathlib.GroupTheory.GroupAction.Primitive

/-! Primitivity transports across the proved equality of actual
inner top images. This asserts only the intermediate top's property,
with no claim of simultaneous primitive outer action or component. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NestedBlockPrimitiveTopTransport
open NestedBlockComponentAction

theorem preprimitive
    {A Ω X Y : Type} [Group A] [MulAction A Ω] [MulAction A X] [MulAction A Y]
    (b : Ω → X) (hb : ∀ (g : A) (ω : Ω), b (g • ω) = g • b ω)
    (hbs : Function.Surjective b)
    (c : X → Y) (hc : ∀ (g : A) (x : X), c (g • x) = g • c x) (y : Y)
    (hprimitive : MulAction.IsPreprimitive (originalBlockComponent c hc y) (InnerFibre c y)) :
    letI := componentAction b hb c hc hbs y
    MulAction.IsPreprimitive
      (OriginalBlockClassBound.Top (A := Component b hb c hc y) (X := InnerFibre c y))
      (InnerFibre c y) := by
  letI := componentAction b hb c hc hbs y
  rw [NestedBlockComponentTopTransport.top_eq b hb hbs c hc y]
  exact hprimitive

end SymmetricSubgroupAsymptotics.NestedBlockPrimitiveTopTransport
