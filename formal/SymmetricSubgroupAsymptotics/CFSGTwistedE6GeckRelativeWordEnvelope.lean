import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckNormalizerEnvelope
import SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedWordClassification

/-! Equal actual lattice actions give a matrix-word ratio in the
proved simultaneous-normalizer envelope. Thus a diagram-compatible
Weyl word can be replaced by a genuinely fixed relative word without
asserting that its lattice-kernel ratio lies in the generated torus. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeWordEnvelope
open CFSGTwistedE6GeckDiagramCovariance CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGTwistedE6WeylChamber
open CFSGTwistedE6FixedWordClassification CFSGTwistedE6GeckNormalizerEnvelope
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoGeckIntegralWord CFSGNormTwoCoordinateRootLineNormalizers
open CFSGNormTwoCoordinateNormalizerSoluble CFSGNormTwoGeckWeylLatticeLinear
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite

theorem linearAction_inverseWord (w : List (Fin 6)) :
    linearAction (inverseWord w)=(linearAction w)⁻¹ :=
  wordLinear_inverseWord A hs hp E6Base E6Index w

theorem identity_word_mem_diagonalNormalizer (K : Type) [Field K]
    (w : List (Fin 6)) (hw : linearAction w = 1) :
    wordUnit A hs hp E6Base E6Index K w ∈ diagonalNormalizer K := by
  refine ⟨⟨?_,?_⟩,wordUnit_mem_canonical A (CartanMatrix.E₆_diag) hs hp
    (CartanMatrix.E₆_off_diag_nonpos) K w⟩
  · rw [word_eq_canonicalWord]
    exact identity_word_normalizes A (CartanMatrix.E₆_diag) hs hp
      (CartanMatrix.E₆_off_diag_nonpos) K w hw false
  · rw [word_eq_canonicalWord]
    exact identity_word_normalizes A (CartanMatrix.E₆_diag) hs hp
      (CartanMatrix.E₆_off_diag_nonpos) K w hw true

theorem same_action_word_ratio_mem (K : Type) [Field K]
    (w v : List (Fin 6)) (he : linearAction w = linearAction v) :
    wordUnit A hs hp E6Base E6Index K w * (wordUnit A hs hp E6Base E6Index K v)⁻¹ ∈
      diagonalNormalizer K := by
  have hlin : linearAction (w ++ inverseWord v) = 1 := by
    rw [linearAction_append,linearAction_inverseWord,he,mul_inv_cancel]
  have hh := identity_word_mem_diagonalNormalizer K (w ++ inverseWord v) hlin
  simpa only [wordUnit_append,wordUnit_inverseWord] using hh

theorem exists_relative_matrix_factor (K : Type) [Field K]
    (w : List (Fin 6))
    (hcomm : ∀ k, diagramRoot (rootAction w k) = rootAction w (diagramRoot k)) :
    ∃ (r : List (Fin 4)) (d : (Matrix GeckIndex GeckIndex K)ˣ),
      d ∈ diagonalNormalizer K ∧
      wordUnit A hs hp E6Base E6Index K w = d * wordUnit A hs hp E6Base E6Index K (expandRelative r) := by
  obtain ⟨r,hr⟩ := exists_relative_word_action w hcomm
  refine ⟨r,wordUnit A hs hp E6Base E6Index K w *
    (wordUnit A hs hp E6Base E6Index K (expandRelative r))⁻¹,
    same_action_word_ratio_mem K w (expandRelative r) hr,?_⟩
  exact (inv_mul_cancel_right _ _).symm

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeWordEnvelope
