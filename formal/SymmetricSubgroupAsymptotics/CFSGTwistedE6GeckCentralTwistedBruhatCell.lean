import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckEnvelopeBlocks
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckNormalizerEnvelopeTwist
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeBruhatCover
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRootSubgroupTwist
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBruhatCover
import Mathlib.Tactic.Group

/-! A literal E6 element fixed modulo the elementary centre has an
actual enlarged relative inversion cell. Central differences remain in
the simultaneous normalizer; no torus recognition is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckCentralTwistedBruhatCell
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckNormalizerEnvelope CFSGTwistedE6GeckNormalizerEnvelopeTwist
open CFSGTwistedE6GeckEnvelopeBlocks CFSGTwistedE6GeckRelativeBruhatCover
open CFSGTwistedE6GeckRootSubgroupTwist CFSGTwistedE6GeckInversionParts
open CFSGTwistedE6GeckSourceAction CFSGTwistedE6FixedWordClassification
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckIntegralWord
open CFSGNormTwoGeckBorelEnvelope CFSGNormTwoCoordinateWeylBlocks
open CFSGNormTwoCoordinateBlockDiagramAction CFSGSerreDiagram
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

theorem unitTwist_wordUnit (K : Type) [Field K] (sigma : K≃+*K) (w : List (Fin 6)) :
    unitTwist K sigma (wordUnit A hs hp E6Base E6Index K w)=
      wordUnit A hs hp E6Base E6Index K (w.map e6Permutation) := by
  simpa only [word_eq_canonicalWord] using unitTwist_word K sigma w

private theorem twisted_cell_rearrange {G : Type*} [Group G]
    (tau : G →* G) (g z b c w w' : G)
    (hf : tau g = z * g) (he : g = b * w * c) (hw : tau w = w') :
    ((z * b)⁻¹ * tau b) * w' * (tau c * c⁻¹) = w := by
  calc
    _ = (z * b)⁻¹ * tau g * c⁻¹ := by rw [he, map_mul, map_mul, hw]; group
    _ = w := by rw [hf, he]; group

theorem twisted_bruhat_cell_block (K : Type) [Field K] (sigma : K ≃+* K)
    (g z b c : (Matrix GeckIndex GeckIndex K)ˣ) (w : List (Fin 6))
    (hz : z ∈ normalizerEnvelope K)
    (hb : b ∈ normalizerEnvelope K) (hc : c ∈ normalizerEnvelope K)
    (htwist : unitTwist K sigma g = z * g)
    (he : g = b * wordUnit A hs
      hp E6Base E6Index K w * c) :
    wordBlockPermutation A hd hs hp ho (w.map e6Permutation) = wordBlockPermutation A hd hs hp ho w := by
  let B := normalizerEnvelope K
  let b₁ := (z * b)⁻¹ * unitTwist K sigma b
  let b₂ := unitTwist K sigma c * c⁻¹
  have hb₁ : b₁ ∈ B := B.mul_mem (B.inv_mem (B.mul_mem hz hb))
    (normalizer_envelope_twist_mem K sigma b hb)
  have hb₂ : b₂ ∈ B := B.mul_mem (normalizer_envelope_twist_mem K sigma c hc) (B.inv_mem hc)
  exact envelope_bruhat_block_unique K (w.map e6Permutation) w b₁ b₂ hb₁ hb₂
    (twisted_cell_rearrange (unitTwist K sigma).toMonoidHom g z b c _ _
      htwist he (unitTwist_wordUnit K sigma w))

theorem central_twisted_bruhat_cell_block (K : Type) [Field K] (sigma : K ≃+* K)
    (g b c : (Matrix GeckIndex GeckIndex K)ˣ) (z : MatrixGroup K)
    (hz : z ∈ Subgroup.center (MatrixGroup K)) (w : List (Fin 6))
    (hb : b ∈ normalizerEnvelope K) (hc : c ∈ normalizerEnvelope K)
    (htwist : unitTwist K sigma g = z.val * g)
    (he : g = b * wordUnit A hs
      hp E6Base E6Index K w * c) :
    wordBlockPermutation A hd hs hp ho (w.map e6Permutation) = wordBlockPermutation A hd hs hp ho w :=
  twisted_bruhat_cell_block K sigma g z.val b c w
    (diagonalNormalizer_le_envelope K (center_mem_diagonalNormalizer K z hz)) hb hc htwist he

theorem exists_central_twisted_relative_cell (K : Type) [Field K] [Finite K]
    (sigma : K ≃+* K) (g : (Matrix GeckIndex GeckIndex K)ˣ)
    (hg : g ∈ MatrixGroup K) (z : MatrixGroup K)
    (hz : z ∈ Subgroup.center (MatrixGroup K))
    (htwist : unitTwist K sigma g = z.val * g) :
    ∃ (r : List (Fin 4)) (b : (Matrix GeckIndex GeckIndex K)ˣ),
      b ∈ normalizerEnvelope K ∧ ∃ v : InversionPart K (expandRelative r),
        g = b * wordUnit A hs
          hp E6Base E6Index K (expandRelative r) * inversionEmbedding K (expandRelative r) v := by
  obtain ⟨w, b, hb, c, hc, he⟩ := CFSGNormTwoCoordinateBruhatCover.canonical_bruhat_cover
    A hd hs
    hp ho K g hg
  have hi := central_twisted_bruhat_cell_block K sigma g b c z hz w
    (borel_le_normalizerEnvelope K hb) (borel_le_normalizerEnvelope K hc) htwist he
  exact exists_relative_inversion_cell_of_commuting_word K g b c w hb hc he
    (CFSGNormTwoCoordinateBlockDiagramAction.block_invariance_root_commutes
      A hd hs hp ho e6Permutation e6_preserves w hi)

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckCentralTwistedBruhatCell
