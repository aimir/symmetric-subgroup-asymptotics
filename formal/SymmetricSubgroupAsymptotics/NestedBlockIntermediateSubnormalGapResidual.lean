import SymmetricSubgroupAsymptotics.NestedBlockPrimitiveTopTransport
import SymmetricSubgroupAsymptotics.LargePrimitiveIntermediateSubnormalGapResidual

/-! The stronger subnormal gap on an actual original nested component,
with only literal Tits/sporadic intermediate-factor residuals. The
returned descriptor acts on the original inner fibre under the original
second-map component; no action or class-count recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NestedBlockIntermediateSubnormalGapResidual
open NestedBlockComponentAction PrimitiveSocleRawStructure LargeTopFiniteModelResidual

theorem subnormal_gap_or_actual_finite_model
    (hCFSG : CFSG.CFSGClassification)
    {A Ω X Y : Type} [Group A] [MulAction A Ω] [MulAction A X] [MulAction A Y]
    [Finite A] [Finite Ω] [Finite X] [Finite Y]
    (b : Ω → X) (hb : ∀ (g : A) (ω : Ω), b (g • ω) = g • b ω)
    (hbs : Function.Surjective b)
    (c : X → Y) (hc : ∀ (g : A) (x : X), c (g • x) = g • c x)
    (y : Y) (k : ℕ) (hk : k = 2 ∨ k = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x) = k)
    (hlarge : 4096 ≤ Nat.card (InnerFibre c y))
    (hprimitive : MulAction.IsPreprimitive (originalBlockComponent c hc y) (InnerFibre c y))
    (L : Subgroup (Component b hb c hc y)) (hL : L.IsSubnormal) :
    Nat.card (ConjClasses L) ^ 3 ≤ 5 ^ (Nat.card (OuterFibre b c y) - 2) ∨
      ∃ D : NonaffineData (originalBlockComponent c hc y) (InnerFibre c y), ∃ i : CFSG.Index,
        RemainingFiniteSimpleType i ∧ Nonempty (D.Simple ≃* i.Model) ∧
          ∃ K : Subgroup D.Simple, K ≠ ⊤ ∧ Nat.card (InnerFibre c y) = K.index ^ D.factorCount ∧
            K.index ^ (4 * Nat.log 2 K.index + 23) <
              Nat.card D.Simple * Nat.card (Outer D.Simple) ∧
            K.index ^ 66 < Nat.card D.Simple * Nat.card (Outer D.Simple) := by
  letI := componentAction b hb c hc hbs y
  have hmap : ∀ (g : Component b hb c hc y) (u : OuterFibre b c y),
      innerMap b c y (g • u) = g • innerMap b c y u :=
    innerMap_equivariant b hb c hc hbs y
  have hs : ∀ x, Nat.card (originalBlockFibre (innerMap b c y) x) = k := by
    intro x
    exact (Nat.card_congr (innerFibreEquiv b c y x)).trans (hsize x.val)
  have hpr := NestedBlockPrimitiveTopTransport.preprimitive b hb hbs c hc y hprimitive
  rcases LargePrimitiveIntermediateSubnormalGapResidual.subnormal_gap_or_actual_finite_model
    hCFSG (innerMap b c y) hmap k hk hs hlarge hpr L hL with h | h
  · exact Or.inl h
  · right
    let P : Subgroup (Equiv.Perm (InnerFibre c y)) → Prop := fun T =>
      ∃ D : NonaffineData T (InnerFibre c y), ∃ i : CFSG.Index,
        RemainingFiniteSimpleType i ∧ Nonempty (D.Simple ≃* i.Model) ∧
          ∃ K : Subgroup D.Simple, K ≠ ⊤ ∧ Nat.card (InnerFibre c y) = K.index ^ D.factorCount ∧
            K.index ^ (4 * Nat.log 2 K.index + 23) <
              Nat.card D.Simple * Nat.card (Outer D.Simple) ∧
            K.index ^ 66 < Nat.card D.Simple * Nat.card (Outer D.Simple)
    have ht : OriginalBlockClassBound.Top
        (A := Component b hb c hc y) (X := InnerFibre c y) = originalBlockComponent c hc y :=
      NestedBlockComponentTopTransport.top_eq b hb hbs c hc y
    exact Eq.mp (congrArg P ht) h

end SymmetricSubgroupAsymptotics.NestedBlockIntermediateSubnormalGapResidual
