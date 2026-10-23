import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckInversionParts
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckEnvelopeBlocks
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateEnvelopeIntersection
import SymmetricSubgroupAsymptotics.CFSGCentralTwistedProductCoordinates

/-! Unique actual E6 inversion and U/diagonal coordinates of a centrally
twisted element retain genuine fixedness in the unipotent coordinates.
Only the diagonal coordinate carries the central difference. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckCentralTwistedCellFactors
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckSourceAction
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckNormalizerEnvelope CFSGTwistedE6GeckNormalizerEnvelopeTwist
open CFSGTwistedE6GeckEnvelopeBlocks CFSGTwistedE6GeckInversionParts
open CFSGTwistedE6GeckAmbientPositiveSylow
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGExceptionalNormalizerWordIdentity CFSGSignedCartanReflections
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckIntegralWord
open CFSGCentralTwistedProductCoordinates
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

def envelopePart (K : Type) [Field K] : Subgroup (Matrix GeckIndex GeckIndex K)ˣ :=
  normalizerEnvelope K

def diagonalPart (K : Type) [Field K] : Subgroup (Matrix GeckIndex GeckIndex K)ˣ :=
  diagonalNormalizer K

theorem envelope_negative_disjoint (K : Type) [Field K] :
    Disjoint (envelopePart K) (Negative K) :=
  CFSGNormTwoCoordinateEnvelopeIntersection.envelope_negative_disjoint A hd hs hp ho K
    E6Signs E6_signs_square E6_signs_cartan (E6_normalizer_word_identity K) (by decide)

theorem positive_diagonalNormalizer_factors_injective (K : Type) [Field K] :
    Function.Injective (fun p : Positive K × diagonalPart K =>
      (p.1.val : (Matrix GeckIndex GeckIndex K)ˣ)*
        (p.2.val : (Matrix GeckIndex GeckIndex K)ˣ)) :=
  CFSGNormTwoCoordinateEnvelopeIntersection.positive_diagonalNormalizer_factors_injective
    A hd hs hp ho K E6Signs E6_signs_square E6_signs_cartan
      (E6_normalizer_word_identity K) (by decide)

theorem envelope_inversion_factors_injective (K : Type) [Field K] (w : List (Fin 6)) :
    Function.Injective (fun p : envelopePart K × InversionPart K w =>
      (p.1.val : (Matrix GeckIndex GeckIndex K)ˣ) *
        wordUnit A hs
          hp E6Base E6Index K w * inversionEmbedding K w p.2) := by
  apply shifted_product_factors_injective _ (Negative K) _ _
    (inversionEmbedding_injective K w) (envelope_negative_disjoint K)
  intro v
  rw [word_eq_canonicalWord]
  exact v.property

theorem central_twisted_cell_coordinates (K : Type) [Field K] (sigma : K ≃+* K)
    (w : List (Fin 6))
    (hW : unitTwist K sigma (wordUnit A hs
      hp E6Base E6Index K w) =
      wordUnit A hs
        hp E6Base E6Index K w)
    (z : MatrixGroup K) (hz : z ∈ Subgroup.center (MatrixGroup K))
    (b : envelopePart K) (v : InversionPart K w)
    (htwist : unitTwist K sigma ((b.val : (Matrix GeckIndex GeckIndex K)ˣ) *
      wordUnit A hs
        hp E6Base E6Index K w * inversionEmbedding K w v) =
      z.val * ((b.val : (Matrix GeckIndex GeckIndex K)ˣ) * wordUnit A hs
        hp E6Base E6Index K w * inversionEmbedding K w v)) :
    unitTwist K sigma (b.val : (Matrix GeckIndex GeckIndex K)ˣ) = z.val * (b.val : (Matrix GeckIndex GeckIndex K)ˣ) ∧
      unitTwist K sigma (inversionEmbedding K w v) = inversionEmbedding K w v := by
  let bt : envelopePart K :=
    ⟨unitTwist K sigma (b.val : (Matrix GeckIndex GeckIndex K)ˣ), normalizer_envelope_twist_mem K sigma (b.val : (Matrix GeckIndex GeckIndex K)ˣ) b.property⟩
  let bz : envelopePart K := ⟨z.val * (b.val : (Matrix GeckIndex GeckIndex K)ˣ),
    (envelopePart K).mul_mem
      (diagonalNormalizer_le_envelope K (center_mem_diagonalNormalizer K z hz)) b.property⟩
  let vt := inversionTwistElement K sigma w hW v
  exact twisted_product_values (unitTwist K sigma).toMonoidHom _ _ z.val
    (inversionEmbedding K w) (envelope_inversion_factors_injective K w)
    b bt bz v vt rfl rfl (inversionTwistElement_value K sigma w hW v) hW htwist

theorem exists_central_twisted_envelope_factors (K : Type) [Field K] (sigma : K ≃+* K)
    (b : (Matrix GeckIndex GeckIndex K)ˣ) (hb : b ∈ envelopePart K)
    (z : MatrixGroup K) (hz : z ∈ Subgroup.center (MatrixGroup K))
    (htwist : unitTwist K sigma b = z.val * b) :
    ∃ u : (Matrix GeckIndex GeckIndex K)ˣ, u∈Positive K ∧ unitTwist K sigma u=u ∧
      ∃ d : (Matrix GeckIndex GeckIndex K)ˣ, d∈diagonalPart K ∧
        unitTwist K sigma d=z.val*d ∧ b=u*d := by
  obtain ⟨u, hu, d, hD, _, he⟩ := normalizer_envelope_factor K b hb
  have htu : unitTwist K sigma u ∈ Positive K := by
    have hm : unitTwist K sigma u ∈ (Positive K).map (unitTwist K sigma).toMonoidHom :=
      ⟨u, hu, rfl⟩
    rwa [positive_twist_map] at hm
  let ut : Positive K := ⟨unitTwist K sigma u, htu⟩
  let dt : diagonalPart K :=
    ⟨unitTwist K sigma d, diagonalNormalizer_twist_mem K sigma d hD⟩
  let dz : diagonalPart K :=
    ⟨z.val * d, (diagonalPart K).mul_mem (center_mem_diagonalNormalizer K z hz) hD⟩
  have hc : Commute z.val u := by
    have hh := congrArg (fun a : MatrixGroup K => a.val)
      (Subgroup.mem_center_iff.mp hz ⟨u, positive_le_matrixGroup K hu⟩)
    exact hh.symm
  have htw : unitTwist K sigma (u * d) = z.val * (u * d) := by rwa [← he]
  have hh := twisted_diagonal_values (unitTwist K sigma).toMonoidHom
    (Positive K) (diagonalPart K) (positive_diagonalNormalizer_factors_injective K)
    z.val ⟨u, hu⟩ ut ⟨d, hD⟩ dt dz rfl rfl rfl hc htw
  exact ⟨u, hu, hh.1, d, hD, hh.2, he⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckCentralTwistedCellFactors
