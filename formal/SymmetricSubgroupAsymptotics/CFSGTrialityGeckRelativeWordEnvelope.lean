import SymmetricSubgroupAsymptotics.CFSGTrialityGeckNormalizerEnvelope
import SymmetricSubgroupAsymptotics.CFSGTrialityD4FixedWordClassification

/-! Equal actual lattice actions give a matrix-word ratio in the
proved simultaneous-normalizer envelope. Thus a triality-compatible
Weyl word can be replaced by a genuinely fixed relative word without
asserting that its lattice-kernel ratio lies in the generated torus. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeWordEnvelope
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityD4InvariantRoots CFSGTrialityD4WordDiscriminant
open CFSGTrialityD4WordCancellation CFSGTrialityD4FixedWordClassification
open CFSGTrialityRelativeWordLanguage CFSGTrialityGeckNormalizerEnvelope
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoGeckIntegralWord CFSGNormTwoCoordinateRootLineNormalizers
open CFSGNormTwoCoordinateNormalizerSoluble
local notation "A" => CartanMatrix.D 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite

theorem identity_word_mem_diagonalNormalizer (K : Type) [Field K]
    (w : List (Fin 4)) (hw : linearAction w = 1) :
    wordUnit A hs hp Base Index K w ∈ diagonalNormalizer K := by
  refine ⟨⟨?_,?_⟩,wordUnit_mem_canonical A (CartanMatrix.D_diag 4) hs hp
    (CartanMatrix.D_off_diag_nonpos 4) K w⟩
  · rw [word_eq_canonicalWord]
    exact identity_word_normalizes A (CartanMatrix.D_diag 4) hs hp
      (CartanMatrix.D_off_diag_nonpos 4) K w hw false
  · rw [word_eq_canonicalWord]
    exact identity_word_normalizes A (CartanMatrix.D_diag 4) hs hp
      (CartanMatrix.D_off_diag_nonpos 4) K w hw true

theorem same_action_word_ratio_mem (K : Type) [Field K]
    (w v : List (Fin 4)) (he : linearAction w = linearAction v) :
    wordUnit A hs hp Base Index K w * (wordUnit A hs hp Base Index K v)⁻¹ ∈
      diagonalNormalizer K := by
  have hlin : linearAction (w ++ inverseWord v) = 1 := by
    rw [linearAction_append,linearAction_inverseWord,he,mul_inv_cancel]
  have hh := identity_word_mem_diagonalNormalizer K (w ++ inverseWord v) hlin
  simpa only [wordUnit_append,wordUnit_inverseWord] using hh

theorem exists_relative_matrix_factor (K : Type) [Field K]
    (w : List (Fin 4))
    (hcomm : ∀ k, diagramRoot (rootAction w k) = rootAction w (diagramRoot k)) :
    ∃ (r : List Bool) (d : (Matrix GeckIndex GeckIndex K)ˣ),
      d ∈ diagonalNormalizer K ∧
      wordUnit A hs hp Base Index K w = d * wordUnit A hs hp Base Index K (expandRelative r) := by
  obtain ⟨r,hr⟩ := exists_relative_word_action w hcomm
  refine ⟨r,wordUnit A hs hp Base Index K w *
    (wordUnit A hs hp Base Index K (expandRelative r))⁻¹,
    same_action_word_ratio_mem K w (expandRelative r) hr,?_⟩
  exact (inv_mul_cancel_right _ _).symm

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeWordEnvelope
