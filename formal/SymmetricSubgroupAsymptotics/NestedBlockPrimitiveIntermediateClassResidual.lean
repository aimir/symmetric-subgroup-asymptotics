import SymmetricSubgroupAsymptotics.NestedBlockIntermediateSubnormalGapResidual
import SymmetricSubgroupAsymptotics.SmallTopLargePrimitiveComponentClassBound

/-! A CFSG-facing three-level original block reduction. Small inner
fibres, a large primitive intermediate component and a literal small
outer top give the GM cube, except for actual Tits/sporadic descriptors
in a failed original subnormal coordinate. No primitive outer action,
independent coordinates or class-count callback is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.NestedBlockPrimitiveIntermediateClassResidual
open NestedBlockComponentAction PrimitiveSocleRawStructure LargeTopFiniteModelResidual

theorem class_cube_or_actual_finite_model (hCFSG : CFSG.CFSGClassification)
    {A Ω X Y : Type} [Group A] [MulAction A Ω] [MulAction A X] [MulAction A Y]
    [Finite A] [Finite Ω] [Finite X] [Finite Y] [FaithfulSMul A Ω]
    (b : Ω → X) (hb : ∀ (g : A) (ω : Ω), b (g • ω) = g • b ω)
    (hbs : Function.Surjective b)
    (c : X → Y) (hc : ∀ (g : A) (x : X), c (g • x) = g • c x)
    (k : ℕ) (hk : k = 2 ∨ k = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x) = k)
    (q : ℕ) (hq : 4096 ≤ q) (hinter : ∀ y, Nat.card (originalBlockFibre c y) = q)
    (hblocks : Nat.card Y = 2 ∨ Nat.card Y = 3)
    (hprimitive : ∀ y, MulAction.IsPreprimitive
      (originalBlockComponent c hc y) (InnerFibre c y)) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) ∨
      ∃ y : Y, ∃ L : Subgroup (Component b hb c hc y),
        L.IsSubnormal ∧ 5 ^ (q * k - 2) < Nat.card (ConjClasses L) ^ 3 ∧
          ∃ D : NonaffineData (originalBlockComponent c hc y) (InnerFibre c y),
            ∃ i : CFSG.Index, RemainingFiniteSimpleType i ∧ Nonempty (D.Simple ≃* i.Model) ∧
              ∃ K : Subgroup D.Simple, K ≠ ⊤ ∧ q = K.index ^ D.factorCount ∧
                K.index ^ (4 * Nat.log 2 K.index + 23) <
                  Nat.card D.Simple * Nat.card (Outer D.Simple) ∧
                K.index ^ 66 < Nat.card D.Simple * Nat.card (Outer D.Simple) := by
  have hs : ∀ y, Nat.card (OuterFibre b c y) = q * k := by
    intro y
    have hf : ∀ x, Nat.card (originalBlockFibre (innerMap b c y) x) = k := by
      intro x
      exact (Nat.card_congr (innerFibreEquiv b c y x)).trans (hsize x.val)
    have h := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre (innerMap b c y) k hf
    rw [hinter y] at h
    exact h
  by_cases hall : ∀ y (L : Subgroup (Component b hb c hc y)), L.IsSubnormal →
      Nat.card (ConjClasses L) ^ 3 ≤ 5 ^ (q * k - 2)
  · have hk2 : 2 ≤ k := by rcases hk with rfl | rfl <;> decide
    have ha : 2 ≤ q * k := by nlinarith
    exact Or.inl
      (SmallTopLargePrimitiveComponentClassBound.class_cube_le_of_subnormal_component_gaps
        (c ∘ b) (composite_equivariant b hb c hc) (q * k) ha hblocks hs hall)
  · simp only [not_forall,_root_.not_imp] at hall
    obtain ⟨y,L,hL,hnot⟩ := hall
    have hl : 4096 ≤ Nat.card (InnerFibre c y) := by rw [hinter y]; exact hq
    rcases NestedBlockIntermediateSubnormalGapResidual.subnormal_gap_or_actual_finite_model
      hCFSG b hb hbs c hc y k hk hsize hl (hprimitive y) L hL with h | h
    · have hg : Nat.card (ConjClasses L) ^ 3 ≤ 5 ^ (q * k - 2) := by
        simpa only [hs y] using h
      exact (hnot hg).elim
    · obtain ⟨D,i,hi,he,K,hK,hdegree,hlog,hbound⟩ := h
      exact Or.inr ⟨y,L,hL,lt_of_not_ge hnot,D,i,hi,he,K,hK,
        (hinter y).symm.trans hdegree,hlog,hbound⟩

end SymmetricSubgroupAsymptotics.NestedBlockPrimitiveIntermediateClassResidual
