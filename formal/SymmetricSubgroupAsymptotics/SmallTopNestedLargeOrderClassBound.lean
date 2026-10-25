import SymmetricSubgroupAsymptotics.LargeSmallFibreSubgroupClassGap
import SymmetricSubgroupAsymptotics.SmallTopLargePrimitiveComponentClassBound

/-! A three-level tail for literal two- or three-point outer tops.
Each original outer component has an actual binary/ternary inner block
action with a large top of proved order. The stronger subgroup gap
pays the outer extension without requiring either top to be primitive. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallTopNestedLargeOrderClassBound

theorem class_cube_le_of_component_block_orders
    {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]
    (b : Ω → X) (hb : ∀ (g : A) (ω : Ω), b (g • ω) = g • b ω)
    (a : ℕ) (ha : 2 ≤ a) (hblocks : Nat.card X = 2 ∨ Nat.card X = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x) = a)
    (Y : X → Type) [∀ x, Finite (Y x)]
    [∀ x, MulAction (originalBlockComponent b hb x) (Y x)]
    (d : ∀ x, originalBlockFibre b x → Y x)
    (hd : ∀ x (g : originalBlockComponent b hb x) (ω : originalBlockFibre b x),
      d x (g • ω) = g • d x ω)
    (c : X → ℕ) (hc : ∀ x, c x = 2 ∨ c x = 3)
    (hinner : ∀ x y, Nat.card (originalBlockFibre (d x) y) = c x)
    (hlarge : ∀ x, 4096 ≤ Nat.card (Y x))
    (horder : ∀ x, Nat.card (OriginalBlockClassBound.Top
      (A := originalBlockComponent b hb x) (X := Y x)) ≤
        Nat.card (Y x) ^ (4 * Nat.log 2 (Nat.card (Y x)) + 30)) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) := by
  apply SmallTopLargePrimitiveComponentClassBound.class_cube_le_of_subnormal_component_gaps
    b hb a ha hblocks hsize
  intro x L _
  have h := LargeSmallFibreSubgroupClassGap.subgroup_class_cube_gap_of_top_order
    (d x) (hd x) (c x) (hc x) (hinner x) (hlarge x) (horder x) L
  simpa only [hsize x] using h

end SymmetricSubgroupAsymptotics.SmallTopNestedLargeOrderClassBound
