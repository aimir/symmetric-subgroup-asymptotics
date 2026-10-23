import SymmetricSubgroupAsymptotics.CFSGTrialityGeckNormalizerEnvelopeTwist
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeWordEnvelope
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionHeightMembership
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBorelRootNormalization

/-! Track precisely the diagonal factors which normalize every actual
root line. This is stronger than membership in the simultaneous U/V
normalizer and does not identify its entire lattice kernel with a torus. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckRootLineDiagonal
open CFSGNormTwoRootPairing CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckNormalizerEnvelopeTwist
open CFSGTrialityD4WordDiscriminant CFSGTrialityD4WordCancellation
open CFSGTrialityD4FixedWordClassification CFSGTrialityD4InvariantRoots
open CFSGTrialityRelativeWordLanguage CFSGTrialityGeckRelativeWordEnvelope
open CFSGTrialityGeckNormalizerEnvelope CFSGTrialityGeckSectionHeightMembership
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckIntegralWord CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoCoordinateRootLineNormalizers CFSGNormTwoCoordinateBorelRootNormalization
open CFSGNormTwoGeckBorelEnvelope
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) :=
  Classical.decEq _

local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4

def rootLineDiagonal (K : Type) [Field K] :
    Subgroup ((Matrix GeckIndex GeckIndex K)ˣ) :=
  diagonalNormalizer K ⊓ ⨅ k, Subgroup.normalizer {g : (Matrix GeckIndex GeckIndex K)ˣ | g ∈ RootLine K k}

theorem rootLineDiagonal_le_diagonal (K : Type) [Field K] :
    rootLineDiagonal K ≤ diagonalNormalizer K := inf_le_left

theorem rootLineDiagonal_le_root_normalizer (K : Type) [Field K]
    (k : Roots A) : rootLineDiagonal K ≤ Subgroup.normalizer {g : (Matrix GeckIndex GeckIndex K)ˣ | g ∈ RootLine K k} :=
  inf_le_right.trans (iInf_le _ k)

theorem torus_le_rootLineDiagonal (K : Type) [Field K] :
    torusGroup A hs hp Base Index K ≤ rootLineDiagonal K := by
  apply le_inf (torus_le_diagonalNormalizer K)
  apply le_iInf
  intro k
  exact torusGroup_le_normalizer_root A hd hs hp ho K k

theorem identity_word_mem_rootLineDiagonal (K : Type) [Field K]
    (w : List (Fin 4)) (hw : linearAction w = 1) :
    wordUnit A hs hp Base Index K w ∈ rootLineDiagonal K := by
  have hlines : wordUnit A hs hp Base Index K w ∈
      (⨅ k : Roots A, Subgroup.normalizer
        {g : (Matrix GeckIndex GeckIndex K)ˣ | g ∈ RootLine K k}) := by
    apply Subgroup.mem_iInf.mpr
    intro k
    apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
    have he := identity_word_root_line A hd hs hp ho K w hw k
    rw [word_eq_canonicalWord]
    exact congrArg (fun H : Subgroup ((Matrix GeckIndex GeckIndex K)ˣ) =>
      {g : (Matrix GeckIndex GeckIndex K)ˣ | g ∈ H}) he
  exact ⟨identity_word_mem_diagonalNormalizer K w hw, hlines⟩

theorem same_action_word_ratio_mem (K : Type) [Field K]
    (w v : List (Fin 4)) (he : linearAction w = linearAction v) :
    wordUnit A hs hp Base Index K w * (wordUnit A hs hp Base Index K v)⁻¹ ∈
      rootLineDiagonal K := by
  have hlin : linearAction (w ++ inverseWord v) = 1 := by
    rw [linearAction_append,linearAction_inverseWord,he,mul_inv_cancel]
  have hh := identity_word_mem_rootLineDiagonal K (w ++ inverseWord v) hlin
  simpa only [wordUnit_append,wordUnit_inverseWord] using hh

theorem exists_relative_matrix_factor (K : Type) [Field K]
    (w : List (Fin 4))
    (hcomm : ∀ k, diagramRoot (rootAction w k) = rootAction w (diagramRoot k)) :
    ∃ (r : List Bool) (d : (Matrix GeckIndex GeckIndex K)ˣ),
      d ∈ rootLineDiagonal K ∧
      wordUnit A hs hp Base Index K w = d * wordUnit A hs hp Base Index K (expandRelative r) := by
  obtain ⟨r,hr⟩ := exists_relative_word_action w hcomm
  refine ⟨r,wordUnit A hs hp Base Index K w *
    (wordUnit A hs hp Base Index K (expandRelative r))⁻¹,
    same_action_word_ratio_mem K w (expandRelative r) hr,?_⟩
  exact (inv_mul_cancel_right _ _).symm

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckRootLineDiagonal
