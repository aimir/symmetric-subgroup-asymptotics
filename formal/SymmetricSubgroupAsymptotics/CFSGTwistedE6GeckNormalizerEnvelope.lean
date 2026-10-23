import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalizerEnvelope
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckAmbientPositiveSylow

/-! The checked simultaneous-normalizer envelope specialized to the literal
E6 Geck image. No identification of its diagonal factor with the generated
torus is required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckNormalizerEnvelope
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckSourceAction CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGExceptionalNormalizerWordIdentity
open CFSGSignedCartanReflections CFSGNormTwoGeckIntegralWord
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckBorelEnvelope
open CFSGNormTwoGeckBorelFactorization CFSGNormTwoGeckBorelNormalization
open CFSGNormTwoCoordinateRootLineNormalizers
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

abbrev diagonalNormalizer (K : Type) [Field K] :=
  CFSGNormTwoCoordinateNormalizerEnvelope.diagonalNormalizer A hd hs hp ho K
abbrev normalizerEnvelope (K : Type) [Field K] :=
  CFSGNormTwoCoordinateNormalizerEnvelope.normalizerEnvelope A hd hs hp ho K

theorem positive_le_envelope (K : Type) [Field K] :
    Positive K ≤ normalizerEnvelope K :=
  CFSGNormTwoCoordinateNormalizerEnvelope.positive_le_envelope A hd hs hp ho K

theorem diagonalNormalizer_le_envelope (K : Type) [Field K] :
    diagonalNormalizer K ≤ normalizerEnvelope K :=
  CFSGNormTwoCoordinateNormalizerEnvelope.diagonalNormalizer_le_envelope A hd hs hp ho K

theorem normalizer_envelope_factor (K : Type) [Field K]
    (g : (Matrix GeckIndex GeckIndex K)ˣ) (hg : g∈normalizerEnvelope K) :
    ∃u : (Matrix GeckIndex GeckIndex K)ˣ,u∈Positive K ∧
      ∃d : (Matrix GeckIndex GeckIndex K)ˣ,d∈diagonalNormalizer K ∧
      (d : Matrix GeckIndex GeckIndex K).IsDiag ∧ g=u*d :=
  CFSGNormTwoCoordinateNormalizerEnvelope.normalizer_envelope_factor A hd hs hp ho K
    E6Signs E6_signs_square E6_signs_cartan (E6_normalizer_word_identity K) g hg

theorem diagonalNormalizer_isDiag (K : Type) [Field K]
    (g : (Matrix GeckIndex GeckIndex K)ˣ) (hg : g∈diagonalNormalizer K) :
    (g : Matrix GeckIndex GeckIndex K).IsDiag :=
  CFSGNormTwoCoordinateNormalizerEnvelope.diagonalNormalizer_isDiag A hd hs hp ho K
    E6Signs E6_signs_square E6_signs_cartan (E6_normalizer_word_identity K) (by decide) g hg

theorem diagonalNormalizer_commute (K : Type) [Field K]
    (g h : diagonalNormalizer K) : Commute g h :=
  CFSGNormTwoCoordinateNormalizerEnvelope.diagonalNormalizer_commute A hd hs hp ho K
    E6Signs E6_signs_square E6_signs_cartan (E6_normalizer_word_identity K) (by decide) g h

theorem torus_le_diagonalNormalizer (K : Type) [Field K] :
    torusGroup A hs hp E6Base E6Index K ≤ diagonalNormalizer K := by
  intro t ht
  refine ⟨⟨?_,?_⟩,torusGroup_le_canonical A hs hp E6Base E6Index K ht⟩
  · exact torusGroup_normalizes A hd hs hp ho K false ht
  · exact torusGroup_normalizes A hd hs hp ho K true ht

theorem borel_le_normalizerEnvelope (K : Type) [Field K] :
    borelEnvelope A hs hp E6Base E6Index K ≤ normalizerEnvelope K :=
  le_inf (borelEnvelope_le_normalizer_positive A hs hp E6Base E6Index K)
    (borelEnvelope_le_canonical A hs hp E6Base E6Index K)

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckNormalizerEnvelope
