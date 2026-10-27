import SymmetricSubgroupAsymptotics.FiniteModelOriginalClassTailInstallers
import SymmetricSubgroupAsymptotics.NestedBlockComponentTopTransport
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockTopRefinement

/-! The fixed-model small-fibre tail on an actual nested component.
The induced top is identified with the SAME intermediate component by
innerHom_range. The original F and its model equivalence are transported
along that literal subgroup equality; no new classification is chosen.
Every subgroup of the nested component is retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteModelNestedClassTailInstaller
open PrimitiveSocleRawStructure OriginalBlockClassBound NestedBlockComponentAction

theorem finite_family_nested_threshold {ι : Type} [Finite ι]
    (M : ι → Type) [∀ i,Group (M i)] :
    ∃ N : ℕ,∀ {A Ω X Y : Type} [Group A]
      [MulAction A Ω] [MulAction A X] [MulAction A Y]
      [Finite A] [Finite Ω] [Finite X] [Finite Y]
      (b : Ω → X) (hb : ∀ (g : A) (ω : Ω),b (g • ω)=g • b ω)
      (hbs : Function.Surjective b)
      (c : X → Y) (hc : ∀ (g : A) (x : X),c (g • x)=g • c x)
      (a : ℕ) (ha : a=2 ∨ a=3)
      (hsize : ∀ x,Nat.card (originalBlockFibre b x)=a)
      (y : Y) (F : NonaffineData (originalBlockComponent c hc y) (InnerFibre c y))
      (i : ι) (e : F.Simple ≃* M i),N≤Nat.card (InnerFibre c y) →
      ∀ L : Subgroup (Component b hb c hc y),
      Nat.card (ConjClasses L)^3≤5^(Nat.card (OuterFibre b c y)-2) := by
  obtain ⟨N,hN⟩ := FiniteModelOriginalClassTailInstallers.finite_family_small_fibre_threshold M
  refine ⟨N,?_⟩
  intro A Ω X Y _ _ _ _ _ _ _ _ b hb hbs c hc a ha hsize y F i e hlarge L
  letI := componentAction b hb c hc hbs y
  have hf : ∀ x,Nat.card (originalBlockFibre (innerMap b c y) x)=a := by
    intro x
    exact (Nat.card_congr (innerFibreEquiv b c y x)).trans (hsize x.val)
  have htop : Top (A := Component b hb c hc y) (X := InnerFibre c y)=
      originalBlockComponent c hc y :=
    NestedBlockComponentTopTransport.top_eq b hb hbs c hc y
  have hactual := hN (A := Component b hb c hc y)
    (Ω := OuterFibre b c y) (X := InnerFibre c y)
    (innerMap b c y) (innerMap_equivariant b hb c hc hbs y) a ha hf
  rw [htop] at hactual
  exact hactual F i e hlarge L

theorem finite_family_original_refinement_threshold {ι : Type} [Finite ι]
    (M : ι → Type) [∀ i,Group (M i)] :
    ∃ N : ℕ,∀ {A Ω : Type} [Group A] [MulAction A Ω]
      [MulAction.IsPretransitive A Ω] [Finite A] [Finite Ω]
      {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)
      (hsmall : Nat.card D.Fibre=2 ∨ Nat.card D.Fibre=3),
      letI := D.top_pretransitive
      ∀ E : OriginalMinimalBlock (A := D.Top) D.base,
      letI := OriginalMinimalBlockTopRefinement.action D E
      ∀ (y : E.Points)
        (F : NonaffineData
          (originalBlockComponent (A := A) (OriginalMinimalBlockTopRefinement.map D E)
            (OriginalMinimalBlockTopRefinement.map_equivariant D E) y)
          (originalBlockFibre (OriginalMinimalBlockTopRefinement.map D E) y))
        (i : ι) (e : F.Simple ≃* M i),N≤Nat.card E.Fibre →
      ∀ L : Subgroup (Component D.map D.map_equivariant
        (OriginalMinimalBlockTopRefinement.map D E)
        (OriginalMinimalBlockTopRefinement.map_equivariant D E) y),
      Nat.card (ConjClasses L)^3≤5^(Nat.card E.Fibre*Nat.card D.Fibre-2) := by
  obtain ⟨N,hN⟩ := finite_family_nested_threshold M
  refine ⟨N,?_⟩
  intro A Ω _ _ _ _ _ ω₀ D hsmall
  letI := D.top_pretransitive
  intro E
  letI := OriginalMinimalBlockTopRefinement.action D E
  intro y F i e hlarge L
  let c := OriginalMinimalBlockTopRefinement.map D E
  have hc : ∀ (g : A) (x : D.Points),c (g • x)=g • c x :=
    OriginalMinimalBlockTopRefinement.map_equivariant D E
  have hinner : Nat.card (InnerFibre c y)=Nat.card E.Fibre :=
    OriginalMinimalBlockTopRefinement.fibre_card_at D E y
  have houter : Nat.card (OuterFibre D.map c y)=Nat.card E.Fibre*Nat.card D.Fibre := by
    have hf : ∀ x,Nat.card (originalBlockFibre (innerMap D.map c y) x)=Nat.card D.Fibre := by
      intro x
      exact (Nat.card_congr (innerFibreEquiv D.map c y x)).trans (D.fibre_card_at x.val)
    have hh := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre
      (innerMap D.map c y) (Nat.card D.Fibre) hf
    rw [hinner] at hh
    exact hh
  have hh := hN D.map D.map_equivariant D.map_surjective c hc
    (Nat.card D.Fibre) hsmall D.fibre_card_at y F i e
    (by simpa only [hinner] using hlarge) L
  simpa only [houter] using hh

end SymmetricSubgroupAsymptotics.FiniteModelNestedClassTailInstaller
