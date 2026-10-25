import SymmetricSubgroupAsymptotics.OriginalBinaryBlockSubnormalClassGap
import SymmetricSubgroupAsymptotics.NestedBlockComponentTopTransport
import SymmetricSubgroupAsymptotics.SmallTopLargePrimitiveComponentClassBound
import SymmetricSubgroupAsymptotics.PrimitiveBlockFibre

/-! A literal three-level binary block action with an actual subnormal
symmetric top in every intermediate component. All coordinate images
remain in the original action; no subnormal subgroup is assumed to act
transitively. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.NestedBinarySubnormalSymmetricTopClassBound
open NestedBlockComponentAction

variable {A Ω X Y : Type} [Group A] [MulAction A Ω] [MulAction A X] [MulAction A Y]

private theorem component_inner_pretransitive
    [MulAction.IsPretransitive A X]
    (b : Ω → X) (hb : ∀ (g : A) (ω : Ω), b (g • ω)=g • b ω)
    (hbs : Function.Surjective b)
    (c : X → Y) (hc : ∀ (g : A) (x : X), c (g • x)=g • c x) (y : Y) :
    letI := componentAction b hb c hc hbs y
    MulAction.IsPretransitive (Component b hb c hc y) (InnerFibre c y) := by
  letI := componentAction b hb c hc hbs y
  letI := sourceInnerAction c hc y
  letI : MulAction.IsPretransitive (Source (A := A) y) (InnerFibre c y) :=
    originalBlockStabilizer_pretransitive c hc y
  constructor
  intro x z
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Source (A := A) y) x z
  refine ⟨projection b hb c hc y g,?_⟩
  change innerHom b hb c hc hbs y (projection b hb c hc y g) x=z
  rw [innerHom_projection]
  exact hg

theorem class_cube_le
    [Finite A] [Finite Ω] [Finite X] [Finite Y] [FaithfulSMul A Ω]
    [MulAction.IsPretransitive A X]
    (b : Ω → X) (hb : ∀ (g : A) (ω : Ω), b (g • ω)=g • b ω)
    (hbs : Function.Surjective b)
    (c : X → Y) (hc : ∀ (g : A) (x : X), c (g • x)=g • c x)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x)=2)
    (q : ℕ) (hq : 10 ≤ q) (hinter : ∀ y, Nat.card (originalBlockFibre c y)=q)
    (hblocks : Nat.card Y=2 ∨ Nat.card Y=3)
    (hTop : ∀ y, (originalBlockComponent c hc y).IsSubnormal) :
    Nat.card (ConjClasses A)^3 ≤ 5^(Nat.card Ω-1) := by
  have hs : ∀ y, Nat.card (OuterFibre b c y)=q*2 := by
    intro y
    have hf : ∀ x, Nat.card (originalBlockFibre (innerMap b c y) x)=2 := by
      intro x
      exact (Nat.card_congr (innerFibreEquiv b c y x)).trans (hsize x.val)
    have h := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre (innerMap b c y) 2 hf
    rw [hinter y] at h
    exact h
  apply SmallTopLargePrimitiveComponentClassBound.class_cube_le_of_subnormal_component_gaps
    (c ∘ b) (composite_equivariant b hb c hc) (q*2) (by omega) hblocks hs
  intro y H hH
  letI := componentAction b hb c hc hbs y
  letI : MulAction.IsPretransitive (Component b hb c hc y) (InnerFibre c y) :=
    component_inner_pretransitive b hb hbs c hc y
  have hq' : 10 ≤ Nat.card (InnerFibre c y) := by rw [hinter y]; exact hq
  letI : Nontrivial (InnerFibre c y) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let x₀ : InnerFibre c y := Classical.choice inferInstance
  have htwo : Nat.card (originalBlockFibre (innerMap b c y) x₀)=2 :=
    (Nat.card_congr (innerFibreEquiv b c y x₀)).trans (hsize x₀.val)
  have htop : (OriginalBlockClassBound.Top
      (A := Component b hb c hc y) (X := InnerFibre c y)).IsSubnormal := by
    rw [NestedBlockComponentTopTransport.top_eq b hb hbs c hc y]
    exact hTop y
  have h := OriginalBinaryBlockSubnormalClassGap.subnormal_class_cube_gap_at_original_degree
    (innerMap b c y) (innerMap_equivariant b hb c hc hbs y) x₀ htwo hq' htop H hH
  simpa only [hs y] using h

end SymmetricSubgroupAsymptotics.NestedBinarySubnormalSymmetricTopClassBound
