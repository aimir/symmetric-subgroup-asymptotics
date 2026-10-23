import SymmetricSubgroupAsymptotics.CFSGTrialityGeckEnvelopeBlocks
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckNormalizerEnvelopeTwist
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeBruhatCover
import Mathlib.Tactic.Group

/-! Bruhat-cell invariance also holds for an element fixed modulo the
actual elementary-group centre. The centre is kept inside the proved
diagonal normalizer, with no scalar or literal-torus identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckCentralTwistedBruhatCell
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckMatrixTwist CFSGTrialityGeckNormalizerEnvelope
open CFSGTrialityGeckNormalizerEnvelopeTwist CFSGTrialityGeckEnvelopeBlocks
open CFSGTrialityD4SeparatingWeight CFSGTrialityGeckWeylBlocks
open CFSGTrialityGeckFixedBruhatCell CFSGTrialityGeckRelativeBruhatCover
open CFSGTrialityGeckSourceWordAction CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckBorelEnvelope CFSGTrialityRelativeWordLanguage
open CFSGTrialityGeckBruhatCellFactors
local instance : LinearOrder WeightBlock := blockOrder

private theorem twisted_cell_rearrange {G : Type*} [Group G]
    (tau : G →* G) (g z b c w w' : G)
    (hf : tau g = z * g) (he : g = b * w * c) (hw : tau w = w') :
    ((z * b)⁻¹ * tau b) * w' * (tau c * c⁻¹) = w := by
  calc
    _ = (z * b)⁻¹ * tau g * c⁻¹ := by rw [he, map_mul, map_mul, hw]; group
    _ = w := by rw [hf, he]; group

theorem twisted_bruhat_cell_block (K : Type) [Field K] (sigma : K ≃+* K)
    (g z b c : (Matrix GeckIndex GeckIndex K)ˣ) (w : List (Fin 4))
    (hz : z ∈ normalizerEnvelope K)
    (hb : b ∈ normalizerEnvelope K) (hc : c ∈ normalizerEnvelope K)
    (htwist : unitTwist K sigma g = z * g)
    (he : g = b * wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K w * c) :
    wordBlockPermutation (w.map CFSGSerreDiagram.trialityPermutation) = wordBlockPermutation w := by
  let B := normalizerEnvelope K
  let b₁ := (z * b)⁻¹ * unitTwist K sigma b
  let b₂ := unitTwist K sigma c * c⁻¹
  have hb₁ : b₁ ∈ B := B.mul_mem (B.inv_mem (B.mul_mem hz hb))
    (normalizer_envelope_twist_mem K sigma b hb)
  have hb₂ : b₂ ∈ B := B.mul_mem (normalizer_envelope_twist_mem K sigma c hc) (B.inv_mem hc)
  exact CFSGBlockMonomialBruhatUniqueness.block_bruhat_permutation_unique
    geckBlock geckBlock_surjective b₁ b₂ _ _
    (envelope_block_triangular K b₁ hb₁) (envelope_block_triangular K b₂ hb₂)
    _ _ (word_block_support K _) (word_block_support K _)
    (twisted_cell_rearrange (unitTwist K sigma).toMonoidHom g z b c _ _
      htwist he (unitTwist_wordUnit K sigma w))

theorem central_twisted_bruhat_cell_block (K : Type) [Field K] (sigma : K ≃+* K)
    (g b c : (Matrix GeckIndex GeckIndex K)ˣ) (z : MatrixGroup K)
    (hz : z ∈ Subgroup.center (MatrixGroup K)) (w : List (Fin 4))
    (hb : b ∈ normalizerEnvelope K) (hc : c ∈ normalizerEnvelope K)
    (htwist : unitTwist K sigma g = z.val * g)
    (he : g = b * wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K w * c) :
    wordBlockPermutation (w.map CFSGSerreDiagram.trialityPermutation) = wordBlockPermutation w :=
  twisted_bruhat_cell_block K sigma g z.val b c w
    (diagonalNormalizer_le_envelope K (center_mem_diagonalNormalizer K z hz)) hb hc htwist he

theorem exists_central_twisted_relative_cell (K : Type) [Field K] [Finite K]
    (sigma : K ≃+* K) (g : (Matrix GeckIndex GeckIndex K)ˣ)
    (hg : g ∈ MatrixGroup K) (z : MatrixGroup K)
    (hz : z ∈ Subgroup.center (MatrixGroup K))
    (htwist : unitTwist K sigma g = z.val * g) :
    ∃ (r : List Bool) (b : (Matrix GeckIndex GeckIndex K)ˣ),
      b ∈ normalizerEnvelope K ∧ ∃ v : InversionPart K (expandRelative r),
        g = b * wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
          D4_positive_definite Base Index K (expandRelative r) * inversionEmbedding K (expandRelative r) v := by
  obtain ⟨w, b, hb, c, hc, he⟩ := CFSGNormTwoCoordinateBruhatCover.canonical_bruhat_cover
    (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K g hg
  have hi := central_twisted_bruhat_cell_block K sigma g b c z hz w
    (borel_le_normalizerEnvelope K hb) (borel_le_normalizerEnvelope K hc) htwist he
  exact exists_relative_inversion_cell_of_commuting_word K g b c w hb hc he
    (block_invariance_root_commutes w hi)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckCentralTwistedBruhatCell
