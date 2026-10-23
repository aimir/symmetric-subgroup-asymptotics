import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRootSubgroupTwist
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelEnvelope

/-! The literal diagram--field twist preserves the actual Geck Borel.
The torus assertion follows from its displayed rank-one words. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckBorelTwist
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckMatrixTwist CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckRootSubgroupTwist CFSGSerreQuadraticMatrix CFSGSerreDiagram
open CFSGNormTwoGeckParameterizedWeyl CFSGNormTwoGeckParameterizedTorus
open CFSGNormTwoGeckBorelEnvelope CFSGNormTwoGeckPositivePGroup

theorem unitTwist_parameterWeyl (K : Type) [Field K] (sigma : K ≃+* K)
    (i : Fin 4) (t : Kˣ) :
    unitTwist K sigma (parameterWeyl (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K i t) =
      parameterWeyl (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index K (trialityPermutation i)
        (Units.map sigma.toMonoidHom t) := by
  simp only [parameterWeyl, map_mul]
  change unitTwist K sigma (canonicalRoot rawData K false i (t : K)) *
      unitTwist K sigma (canonicalRoot rawData K true i (-(t : K)⁻¹)) *
      unitTwist K sigma (canonicalRoot rawData K false i (t : K)) =
    canonicalRoot rawData K false (trialityPermutation i) (sigma (t : K)) *
      canonicalRoot rawData K true (trialityPermutation i) (-(sigma (t : K))⁻¹) *
      canonicalRoot rawData K false (trialityPermutation i) (sigma (t : K))
  simp only [unitTwist_raw_root, map_neg, map_inv₀]

theorem unitTwist_parameterTorus (K : Type) [Field K] (sigma : K ≃+* K)
    (i : Fin 4) (t : Kˣ) :
    unitTwist K sigma (parameterTorus (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K i t) =
      parameterTorus (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index K (trialityPermutation i)
        (Units.map sigma.toMonoidHom t) := by
  simp only [parameterTorus, map_mul, map_inv, unitTwist_parameterWeyl, map_one]

theorem unitTwist_torus_mem (K : Type) [Field K] (sigma : K ≃+* K)
    (t : (Matrix GeckIndex GeckIndex K)ˣ)
    (ht : t ∈ torusGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K) :
    unitTwist K sigma t ∈ torusGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K := by
  let T := torusGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K
  have hle : T ≤ T.comap (unitTwist K sigma).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨⟨i, a⟩, rfl⟩
    change unitTwist K sigma (parameterTorus _ _ _ _ _ K i a) ∈ T
    rw [unitTwist_parameterTorus]
    exact Subgroup.subset_closure ⟨(trialityPermutation i, Units.map sigma.toMonoidHom a), rfl⟩
  exact hle ht

theorem unitTwist_borel_mem (K : Type) [Field K] (sigma : K ≃+* K)
    (b : (Matrix GeckIndex GeckIndex K)ˣ)
    (hb : b ∈ borelEnvelope (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K) :
    unitTwist K sigma b ∈ borelEnvelope (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K := by
  let B := borelEnvelope (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K
  have hU : Positive K ≤ B.comap (unitTwist K sigma).toMonoidHom := by
    intro u hu
    have hm : unitTwist K sigma u ∈ (Positive K).map (unitTwist K sigma).toMonoidHom :=
      ⟨u, hu, rfl⟩
    rw [positive_twist_map] at hm
    have hUB : Positive K ≤ B := le_sup_left
    exact hUB hm
  have hT : torusGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K ≤ B.comap (unitTwist K sigma).toMonoidHom := by
    intro t ht
    have hTB : torusGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K ≤ B := le_sup_right
    exact hTB (unitTwist_torus_mem K sigma t ht)
  exact (sup_le hU hT) hb

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckBorelTwist
