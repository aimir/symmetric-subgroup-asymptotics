import SymmetricSubgroupAsymptotics.CFSGTrialityGeckBorelTwist
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckBruhatBlockUniqueness

/-! The actual Geck Borel has unique positive-times-torus factors.
Their uniqueness, together with the literal twist stability, gives
fixed factors for fixed Borel elements without fixed-point exactness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckBorelUniqueFactors
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckMatrixTwist CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckBorelTwist CFSGTrialityGeckBruhatBlockUniqueness
open CFSGNormTwoGeckBorelEnvelope CFSGNormTwoGeckBorelFactorization

theorem positive_torus_disjoint (K : Type) [Field K] :
    Disjoint (Positive K) (torusGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K) := by
  apply Subgroup.disjoint_def.mpr
  intro x hx ht
  obtain ⟨d, hd⟩ := torus_diagonal_of_mem (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K x ht
  apply Units.ext
  ext i j
  change (x : Matrix GeckIndex GeckIndex K) i j = (1 : Matrix GeckIndex GeckIndex K) i j
  by_cases hij : i = j
  · subst j
    exact positive_separating_strict K hx i i le_rfl
  · rw [hd, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

theorem positive_torus_factors_injective (K : Type) [Field K] :
    Function.Injective (fun p : Positive K ×
      torusGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index K =>
      (p.1.val : (Matrix GeckIndex GeckIndex K)ˣ) * p.2.val) :=
  Subgroup.mul_injective_of_disjoint (positive_torus_disjoint K)

theorem exists_fixed_borel_factors (K : Type) [Field K] (sigma : K ≃+* K)
    (g : (Matrix GeckIndex GeckIndex K)ˣ)
    (hg : g ∈ borelEnvelope (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K)
    (hfixed : unitTwist K sigma g = g) :
    ∃ (u : (Matrix GeckIndex GeckIndex K)ˣ), u ∈ Positive K ∧
      unitTwist K sigma u = u ∧
      ∃ t : (Matrix GeckIndex GeckIndex K)ˣ,
        t ∈ torusGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
          D4_positive_definite Base Index K ∧
        unitTwist K sigma t = t ∧ g = u * t := by
  obtain ⟨u, hu, t, ht, he⟩ := borel_factor (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K g hg
  have htu : unitTwist K sigma u ∈ Positive K := by
    have hm : unitTwist K sigma u ∈ (Positive K).map (unitTwist K sigma).toMonoidHom :=
      ⟨u, hu, rfl⟩
    rwa [positive_twist_map] at hm
  have htt := unitTwist_torus_mem K sigma t ht
  have hp : unitTwist K sigma u * unitTwist K sigma t = u * t := by
    rw [← map_mul, ← he, hfixed]
  have hf := positive_torus_factors_injective K
    (a₁ := (⟨unitTwist K sigma u, htu⟩, ⟨unitTwist K sigma t, htt⟩))
    (a₂ := (⟨u, hu⟩, ⟨t, ht⟩)) hp
  exact ⟨u, hu, congrArg (fun p => p.1.val) hf, t, ht,
    congrArg (fun p => p.2.val) hf, he⟩

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckBorelUniqueFactors
