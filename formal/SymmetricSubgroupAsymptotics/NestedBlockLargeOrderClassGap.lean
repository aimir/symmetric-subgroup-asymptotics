import SymmetricSubgroupAsymptotics.NestedBlockComponentAction
import SymmetricSubgroupAsymptotics.LargeSmallFibreSubgroupClassGap

/-! The large-intermediate-top subgroup gap on a literal nested block
component. Its inner action, fibre sizes and exact top image are derived
from the original maps, before using the proved order budget. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NestedBlockLargeOrderClassGap
open NestedBlockComponentAction

theorem subgroup_class_cube_gap
    {A Ω X Y : Type} [Group A] [MulAction A Ω] [MulAction A X] [MulAction A Y]
    [Finite A] [Finite Ω] [Finite X] [Finite Y]
    (b : Ω → X) (hb : ∀ (g : A) (ω : Ω), b (g • ω) = g • b ω)
    (hbs : Function.Surjective b)
    (c : X → Y) (hc : ∀ (g : A) (x : X), c (g • x) = g • c x)
    (y : Y) (k : ℕ) (hk : k = 2 ∨ k = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x) = k)
    (hlarge : 4096 ≤ Nat.card (InnerFibre c y))
    (horder : Nat.card (originalBlockComponent c hc y) ≤
      Nat.card (InnerFibre c y) ^ (4 * Nat.log 2 (Nat.card (InnerFibre c y)) + 30))
    (L : Subgroup (Component b hb c hc y)) :
    Nat.card (ConjClasses L) ^ 3 ≤ 5 ^ (Nat.card (OuterFibre b c y) - 2) := by
  letI := componentAction b hb c hc hbs y
  have hmap : ∀ (g : Component b hb c hc y) (u : OuterFibre b c y),
      innerMap b c y (g • u) = g • innerMap b c y u :=
    innerMap_equivariant b hb c hc hbs y
  have hs : ∀ x, Nat.card (originalBlockFibre (innerMap b c y) x) = k := by
    intro x
    exact (Nat.card_congr (innerFibreEquiv b c y x)).trans (hsize x.val)
  have ht : MulAction.toPermHom (Component b hb c hc y) (InnerFibre c y) =
      innerHom b hb c hc hbs y := by
    apply MonoidHom.ext
    intro g
    apply Equiv.ext
    intro x
    rfl
  have ho : Nat.card (OriginalBlockClassBound.Top
      (A := Component b hb c hc y) (X := InnerFibre c y)) ≤
        Nat.card (InnerFibre c y) ^ (4 * Nat.log 2 (Nat.card (InnerFibre c y)) + 30) := by
    change Nat.card (MulAction.toPermHom (Component b hb c hc y) (InnerFibre c y)).range ≤ _
    rw [ht,innerHom_range]
    exact horder
  exact LargeSmallFibreSubgroupClassGap.subgroup_class_cube_gap_of_top_order
    (innerMap b c y) hmap k hk hs hlarge ho L

end SymmetricSubgroupAsymptotics.NestedBlockLargeOrderClassGap
