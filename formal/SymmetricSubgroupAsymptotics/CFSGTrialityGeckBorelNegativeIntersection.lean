import SymmetricSubgroupAsymptotics.CFSGTrialityGeckBorelUniqueFactors
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOppositeIntersection
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeight

/-! The actual Geck Borel meets the literal negative unipotent group
trivially. The diagonal entries first force the torus factor to be one;
the remaining assertion is the proved positive/negative intersection. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckBorelNegativeIntersection
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckPositiveTwist CFSGTrialityGeckBruhatBlockUniqueness
open CFSGNormTwoGeckBorelEnvelope CFSGNormTwoGeckBorelFactorization
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckOppositeIntersection
open CFSGNormTwoCoordinateHeight

theorem borel_negative_disjoint (K : Type) [Field K] :
    Disjoint (borelEnvelope (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K)
      (rootGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index K true) := by
  apply Subgroup.disjoint_def.mpr
  intro x hx hv
  obtain ⟨u, hu, t, ht, he⟩ := borel_factor (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K x hx
  obtain ⟨d, hd⟩ := torus_diagonal_of_mem (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K t ht
  have hn := negative_le_strict_opposite (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index coordinateHeight
    (simple_height (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)) K hv
  have hd1 (i : GeckIndex) : (d i : K) = 1 := by
    have hxi : (x : Matrix GeckIndex GeckIndex K) i i = 1 := by
      simpa only [Matrix.one_apply_eq] using hn i i le_rfl
    rw [he, Units.val_mul, hd, Matrix.mul_diagonal] at hxi
    have hui : (u : Matrix GeckIndex GeckIndex K) i i = 1 := by
      simpa only [Matrix.one_apply_eq] using positive_separating_strict K hu i i le_rfl
    simpa only [hui, one_mul] using hxi
  have ht1 : t = 1 := by
    apply Units.ext
    change (t : Matrix GeckIndex GeckIndex K) = (1 : Matrix GeckIndex GeckIndex K)
    rw [hd]
    ext i j
    by_cases hij : i = j
    · subst j; simp only [Matrix.diagonal_apply_eq, hd1, Matrix.one_apply_eq]
    · simp only [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  rw [ht1, mul_one] at he
  have hi : x ∈ rootGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K false ⊓
      rootGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index K true := ⟨he ▸ hu, hv⟩
  rw [positive_inf_negative (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index coordinateHeight
    (simple_height (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)) K, Subgroup.mem_bot] at hi
  exact hi

theorem borel_inf_negative (K : Type) [Field K] :
    borelEnvelope (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K ⊓
      rootGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index K true = ⊥ :=
  (borel_negative_disjoint K).eq_bot

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckBorelNegativeIntersection
