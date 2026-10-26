import SymmetricSubgroupAsymptotics.OriginalMinimalBlockNonaffineShapeResidual
import SymmetricSubgroupAsymptotics.GaronziMarotiBoundedShapeCFSGReduction
import SymmetricSubgroupAsymptotics.SmallFibreKnownModelGlobalClassGap
import SymmetricSubgroupAsymptotics.OriginalSmallTopClassCubeBound
import SymmetricSubgroupAsymptotics.OriginalBinaryFourTopClassCubeBound

/-! Original-action GM induction with a genuine nonaffine bounded shape.
Affine minimal components of degree at least four have been proved away.
No class estimate for all groups of a bounded degree is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.GaronziMarotiNonaffineShapeCFSGReduction

variable (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X]

def ActualSmallFibreResidual : Prop :=
  ∃ ht : MulAction.IsPretransitive G X,
    letI := ht
    ∃ ω₀ : X, ∃ D : OriginalMinimalBlock (A := G) ω₀,
      OriginalMinimalBlockNonaffineShapeResidual.SmallFibreShape D ∧
        ¬ SmallFibreKnownModelGlobalClassGap.HasClosedTop D ∧
        4 ≤ Nat.card D.Points ∧
        (Nat.card D.Fibre=2 → 5 ≤ Nat.card D.Points)

def ActualBoundedNonaffineResidual : Prop :=
  ∃ ht : MulAction.IsPretransitive G X,
    letI := ht
    ∃ ω₀ : X, ∃ D : OriginalMinimalBlock (A := G) ω₀,
      OriginalMinimalBlockNonaffineShapeResidual.BoundedNonaffineComponent D

theorem degree_le_of_small_fibre_residual (h : ActualSmallFibreResidual G X) :
    Nat.card X ≤ 36855 := by
  obtain ⟨ht, ω₀, D, hD, _⟩ := h
  letI := ht
  exact hD.2

theorem degree_le_of_nonaffine_residual (h : ActualBoundedNonaffineResidual G X) :
    Nat.card X ≤ 12285 := by
  obtain ⟨ht, ω₀, D, hD⟩ := h
  letI := ht
  exact OriginalMinimalBlockNonaffineShapeResidual.bounded_degree_of_nonaffine_component D hD

theorem class_cube_or_actual_small_fibre_or_nonaffine_component_or_finite_model
    (hCFSG : CFSG.CFSGClassification) (hn : 4 ≤ Nat.card X)
    (hSmaller : ∀ m : ℕ, m < Nat.card X → 4 ≤ m →
      ∀ L : Subgroup (Equiv.Perm (Fin m)),
        Nat.card (ConjClasses L) ^ 3 ≤ 5 ^ (m - 1)) :
    Nat.card (ConjClasses G) ^ 3 ≤ 5 ^ (Nat.card X - 1) ∨
      ActualSmallFibreResidual G X ∨ ActualBoundedNonaffineResidual G X ∨
        GaronziMarotiBoundedShapeCFSGReduction.ActualFiniteModelResidual G X := by
  by_cases ht : MulAction.IsPretransitive G X
  · letI := ht
    letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    by_cases hp : MulAction.IsPreprimitive G X
    · letI := hp
      rcases PrimitiveAllDegreeReeFFourCompleteCFSGReduction.primitive_subnormal_cube_or_finite_model
          hCFSG G X hn ⊤ (Subgroup.Normal.isSubnormal inferInstance) with h | h
      · have he := conjugacyClass_card_congr (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
        rw [he] at h
        exact Or.inl h
      · have hf : GaronziMarotiBoundedShapeCFSGReduction.ActualFiniteModelResidual G X :=
          Or.inl ⟨hp, h⟩
        exact Or.inr (Or.inr (Or.inr hf))
    · let ω₀ : X := Classical.choice inferInstance
      obtain ⟨D⟩ := originalMinimalBlock_nonempty ω₀ hp
      rcases OriginalMinimalBlockNonaffineShapeResidual.class_cube_or_small_fibre_or_nonaffine_component_or_actual_finite_model
          D hCFSG hSmaller with h | h | h | h
      · exact Or.inl h
      · by_cases hsmallTop : Nat.card D.Points=2 ∨ Nat.card D.Points=3
        · exact Or.inl (D.class_cube_le_of_two_or_three_blocks h.1 hsmallTop)
        by_cases hfourbinary : Nat.card D.Points=4 ∧ Nat.card D.Fibre=2
        · exact Or.inl (D.class_cube_le_of_four_binary_blocks hfourbinary.2 hfourbinary.1)
        by_cases hclosed : SmallFibreKnownModelGlobalClassGap.HasClosedTop D
        · exact Or.inl (SmallFibreKnownModelGlobalClassGap.class_cube_gap_of_closed_top D h.1 hclosed)
        · have htop : 4 ≤ Nat.card D.Points := by
            have := D.degrees_ge_two.2
            omega
          have hbinary : Nat.card D.Fibre=2 → 5 ≤ Nat.card D.Points := by
            intro h2
            omega
          exact Or.inr (Or.inl ⟨ht, ω₀, D, h, hclosed, htop, hbinary⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨ht, ω₀, D, h⟩))
      · have hf : GaronziMarotiBoundedShapeCFSGReduction.ActualFiniteModelResidual G X :=
          Or.inr ⟨ht, ω₀, D, h⟩
        exact Or.inr (Or.inr (Or.inr hf))
  · exact Or.inl (GaronziMarotiIntransitiveReduction.intransitive_step ht hn hSmaller)

theorem minimal_counterexample_has_actual_shape_or_finite_model
    (hCFSG : CFSG.CFSGClassification)
    (n : ℕ) (hn : 4 ≤ n) (L : Subgroup (Equiv.Perm (Fin n)))
    (hbad : 5 ^ (n - 1) < Nat.card (ConjClasses L) ^ 3)
    (hSmaller : ∀ m : ℕ, m < n → 4 ≤ m →
      ∀ H : Subgroup (Equiv.Perm (Fin m)),
        Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (m - 1)) :
    ActualSmallFibreResidual L (Fin n) ∨ ActualBoundedNonaffineResidual L (Fin n) ∨
      GaronziMarotiBoundedShapeCFSGReduction.ActualFiniteModelResidual L (Fin n) := by
  have hs : ∀ m : ℕ, m < Nat.card (Fin n) → 4 ≤ m →
      ∀ H : Subgroup (Equiv.Perm (Fin m)),
        Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (m - 1) := by
    simpa only [Nat.card_fin] using hSmaller
  rcases class_cube_or_actual_small_fibre_or_nonaffine_component_or_finite_model
      L (Fin n) hCFSG (by simpa only [Nat.card_fin] using hn) hs with h | h | h | h
  · have hc : Nat.card (ConjClasses L) ^ 3 ≤ 5 ^ (n - 1) := by
      simpa only [Nat.card_fin] using h
    exact (not_lt_of_ge hc hbad).elim
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

end SymmetricSubgroupAsymptotics.GaronziMarotiNonaffineShapeCFSGReduction
