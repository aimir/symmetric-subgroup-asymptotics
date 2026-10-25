import SymmetricSubgroupAsymptotics.GaronziMarotiNonaffineShapeCFSGReduction
import SymmetricSubgroupAsymptotics.GaronziMarotiGlobalBoundedCounterexample

/-! A global original-action counterexample frontier with no supplied
bounded-degree class estimate. Least-degree failure supplies the actual
strict-smaller IH; the retained bounded shape has small fibres or an
actual nonaffine base component, not an unresolved affine profile. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.GaronziMarotiGlobalNonaffineShapeCounterexample
open GaronziMarotiNonaffineShapeCFSGReduction

theorem garonziMaroti_or_actual_shape_counterexample_or_finite_model
    (hCFSG : CFSG.CFSGClassification) :
    GaronziMarotiConjugacyClassBound ∨
      (∃ n : ℕ, 4 ≤ n ∧ ∃ L : Subgroup (Equiv.Perm (Fin n)),
        5 ^ (n - 1) < Nat.card (ConjClasses L) ^ 3 ∧ ActualSmallFibreResidual L (Fin n)) ∨
      (∃ n : ℕ, 4 ≤ n ∧ ∃ L : Subgroup (Equiv.Perm (Fin n)),
        5 ^ (n - 1) < Nat.card (ConjClasses L) ^ 3 ∧ ActualBoundedNonaffineResidual L (Fin n)) ∨
      (∃ n : ℕ, 4 ≤ n ∧ ∃ L : Subgroup (Equiv.Perm (Fin n)),
        5 ^ (n - 1) < Nat.card (ConjClasses L) ^ 3 ∧
          GaronziMarotiBoundedShapeCFSGReduction.ActualFiniteModelResidual L (Fin n)) := by
  by_cases hcube : ∀ n : ℕ, 4 ≤ n → ∀ L : Subgroup (Equiv.Perm (Fin n)),
      Nat.card (ConjClasses L) ^ 3 ≤ 5 ^ (n - 1)
  · left
    intro n hn L
    exact (GaronziMarotiTransitiveTarget.cube_le_iff_real_bound _ n (by omega)).mp
      (hcube n hn L)
  · push_neg at hcube
    obtain ⟨n, hn, L, hbad⟩ := hcube
    obtain ⟨m, _, hm, H, hH, hSmaller⟩ :=
      GaronziMarotiGlobalBoundedCounterexample.exists_minimal_counterexample n hn L hbad
    rcases minimal_counterexample_has_actual_shape_or_finite_model
        hCFSG m hm H hH hSmaller with h | h | h
    · exact Or.inr (Or.inl ⟨m, hm, H, hH, h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨m, hm, H, hH, h⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨m, hm, H, hH, h⟩))

end SymmetricSubgroupAsymptotics.GaronziMarotiGlobalNonaffineShapeCounterexample
