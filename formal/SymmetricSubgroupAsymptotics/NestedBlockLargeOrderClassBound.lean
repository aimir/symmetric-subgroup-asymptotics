import SymmetricSubgroupAsymptotics.NestedBlockLargeOrderClassGap
import SymmetricSubgroupAsymptotics.SmallTopLargePrimitiveComponentClassBound

/-! The original three-level ordered tail: small inner fibres, a large
intermediate block degree, and a literal two- or three-point outer top.
All intermediate component orders refer to the original second map.
No simultaneous primitivity or independent-kernel premise is required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NestedBlockLargeOrderClassBound
open NestedBlockComponentAction

theorem class_cube_le
    {A Ω X Y : Type} [Group A] [MulAction A Ω] [MulAction A X] [MulAction A Y]
    [Finite A] [Finite Ω] [Finite X] [Finite Y] [FaithfulSMul A Ω]
    (b : Ω → X) (hb : ∀ (g : A) (ω : Ω), b (g • ω) = g • b ω)
    (hbs : Function.Surjective b)
    (c : X → Y) (hc : ∀ (g : A) (x : X), c (g • x) = g • c x)
    (k : ℕ) (hk : k = 2 ∨ k = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x) = k)
    (q : ℕ) (hq : 4096 ≤ q) (hinter : ∀ y, Nat.card (originalBlockFibre c y) = q)
    (hblocks : Nat.card Y = 2 ∨ Nat.card Y = 3)
    (horder : ∀ y, Nat.card (originalBlockComponent c hc y) ≤
      q ^ (4 * Nat.log 2 q + 30)) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) := by
  have hs : ∀ y, Nat.card (OuterFibre b c y) = q * k := by
    intro y
    have hf : ∀ x, Nat.card (originalBlockFibre (innerMap b c y) x) = k := by
      intro x
      exact (Nat.card_congr (innerFibreEquiv b c y x)).trans (hsize x.val)
    have h := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre (innerMap b c y) k hf
    rw [hinter y] at h
    exact h
  have hk2 : 2 ≤ k := by rcases hk with rfl | rfl <;> decide
  have ha : 2 ≤ q * k := by nlinarith
  apply SmallTopLargePrimitiveComponentClassBound.class_cube_le_of_subnormal_component_gaps
    (c ∘ b) (composite_equivariant b hb c hc) (q * k) ha hblocks hs
  intro y L _
  have hl : 4096 ≤ Nat.card (InnerFibre c y) := by rw [hinter y]; exact hq
  have ho : Nat.card (originalBlockComponent c hc y) ≤
      Nat.card (InnerFibre c y) ^ (4 * Nat.log 2 (Nat.card (InnerFibre c y)) + 30) := by
    simpa only [hinter y] using horder y
  have h := NestedBlockLargeOrderClassGap.subgroup_class_cube_gap
    b hb hbs c hc y k hk hsize hl ho L
  simpa only [hs y] using h

end SymmetricSubgroupAsymptotics.NestedBlockLargeOrderClassBound
