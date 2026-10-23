import SymmetricSubgroupAsymptotics.CFSGTrialityGeckNormalizerEnvelope
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMatrixGroupTwist
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckBorelTwist

/-! The enlarged simultaneous-normalizer envelope is stable under the
literal diagram--field twist. Torus inclusion is only one containment;
no converse torus recognition is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckNormalizerEnvelopeTwist
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckNormalizerEnvelope CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckMatrixTwist
open CFSGTrialityGeckMatrixGroupTwist CFSGTrialityGeckRootSubgroupTwist
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckBorelEnvelope
open CFSGNormTwoGeckBorelNormalization CFSGNormTwoCoordinateRootLineNormalizers
open CFSGSerreQuadraticMatrix CFSGSerreDiagram
local notation "A" => CartanMatrix.D 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite

theorem negative_twist_map (K : Type) [Field K] (sigma : K ≃+* K) :
    (Negative K).map (unitTwist K sigma).toMonoidHom = Negative K := by
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨⟨i,t⟩,rfl⟩
    change unitTwist K sigma (canonicalRoot rawData K true i t) ∈ Negative K
    rw [unitTwist_raw_root]
    exact Subgroup.subset_closure ⟨(trialityPermutation i,sigma t),rfl⟩
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨⟨i,t⟩,rfl⟩
    refine ⟨canonicalRoot rawData K true (trialityPermutation.symm i) (sigma.symm t),
      Subgroup.subset_closure ⟨(trialityPermutation.symm i,sigma.symm t),rfl⟩,?_⟩
    change unitTwist K sigma (canonicalRoot rawData K true
      (trialityPermutation.symm i) (sigma.symm t)) = _
    rw [unitTwist_raw_root,Equiv.apply_symm_apply,RingEquiv.apply_symm_apply]
    rfl

theorem normalizer_envelope_twist_mem (K : Type) [Field K] (sigma : K ≃+* K)
    (g : (Matrix GeckIndex GeckIndex K)ˣ) (hg : g ∈ normalizerEnvelope K) :
    unitTwist K sigma g ∈ normalizerEnvelope K := by
  have hn := Subgroup.le_normalizer_map (unitTwist K sigma).toMonoidHom ⟨g,hg.1,rfl⟩
  rw [positive_twist_map K sigma] at hn
  have hh : unitTwist K sigma g ∈ (MatrixGroup K).map (unitTwist K sigma).toMonoidHom :=
    ⟨g,hg.2,rfl⟩
  rw [matrixGroup_twist_map K sigma] at hh
  exact ⟨hn,hh⟩

theorem diagonalNormalizer_twist_mem (K : Type) [Field K] (sigma : K ≃+* K)
    (d : (Matrix GeckIndex GeckIndex K)ˣ) (hd : d ∈ diagonalNormalizer K) :
    unitTwist K sigma d ∈ diagonalNormalizer K := by
  have he := normalizer_envelope_twist_mem K sigma d (diagonalNormalizer_le_envelope K hd)
  have hn := Subgroup.le_normalizer_map (unitTwist K sigma).toMonoidHom ⟨d,hd.1.2,rfl⟩
  rw [negative_twist_map K sigma] at hn
  exact ⟨⟨he.1,hn⟩,he.2⟩

theorem torus_le_diagonalNormalizer (K : Type) [Field K] :
    torusGroup A hs hp Base Index K ≤ diagonalNormalizer K := by
  intro t ht
  refine ⟨⟨?_,?_⟩,torusGroup_le_canonical A hs hp Base Index K ht⟩
  · exact torusGroup_normalizes A (CartanMatrix.D_diag 4) hs hp
      (CartanMatrix.D_off_diag_nonpos 4) K false ht
  · exact torusGroup_normalizes A (CartanMatrix.D_diag 4) hs hp
      (CartanMatrix.D_off_diag_nonpos 4) K true ht

theorem borel_le_normalizerEnvelope (K : Type) [Field K] :
    borelEnvelope A hs hp Base Index K ≤ normalizerEnvelope K :=
  le_inf (borelEnvelope_le_normalizer_positive A hs hp Base Index K)
    (borelEnvelope_le_canonical A hs hp Base Index K)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckNormalizerEnvelopeTwist
