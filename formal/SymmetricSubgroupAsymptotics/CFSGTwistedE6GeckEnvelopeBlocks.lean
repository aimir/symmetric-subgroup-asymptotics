import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckNormalizerEnvelope
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBlockDiagramAction
import Mathlib.GroupTheory.Subgroup.Center

/-! Central elements of the literal E6 elementary image belong to the
simultaneous normalizer. Block uniqueness is inherited from the generic
actual coordinate-group envelope. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckEnvelopeBlocks
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckSourceAction
open CFSGTwistedE6GeckNormalizerEnvelope CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckAmbientPositiveSylow CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGExceptionalNormalizerWordIdentity
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoCoordinateWeylBlocks
open CFSGNormTwoGeckWeylWordDegree CFSGSignedCartanReflections
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

private theorem center_normalizes_subgroup {G : Type*} [Group G]
    (H P : Subgroup G) (hPH : P ≤ H) (z : H) (hz : z ∈ Subgroup.center H) :
    z.val ∈ Subgroup.normalizer (P : Set G) := by
  have he (x : G) (hx : x ∈ P) : z.val*x*z.val⁻¹ = x := by
    have hh := congrArg (fun y : H => y.val)
      (Subgroup.mem_center_iff.mp hz ⟨x,hPH hx⟩)
    change x*z.val = z.val*x at hh
    rw [←hh,mul_assoc,mul_inv_cancel,mul_one]
  have hm : P.map (MulAut.conj z.val).toMonoidHom = P := by
    apply Subgroup.ext
    intro x
    constructor
    · rintro ⟨y,hy,rfl⟩
      change z.val*y*z.val⁻¹ ∈ P
      rw [he y hy]
      exact hy
    · intro hx
      exact ⟨x,hx,he x hx⟩
  apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
  exact congrArg (fun Q : Subgroup G => (Q : Set G)) hm

theorem center_mem_diagonalNormalizer (K : Type) [Field K]
    (z : MatrixGroup K) (hz : z ∈ Subgroup.center (MatrixGroup K)) :
    z.val ∈ diagonalNormalizer K := by
  have hV : Negative K ≤ MatrixGroup K := by
    change rootGroup A hs
      hp E6Base E6Index K true ≤
        CFSGSerreQuadraticMatrix.canonicalElementaryGroup
          (CFSGNormTwoGeckIntegralRealization.realizationData A
            hs hp E6Base E6Index) K
    rw [←positive_sup_negative A hs
      hp E6Base E6Index K]
    exact le_sup_right
  exact ⟨⟨center_normalizes_subgroup (MatrixGroup K) (Positive K)
    (positive_le_matrixGroup K) z hz,
    center_normalizes_subgroup (MatrixGroup K) (Negative K) hV z hz⟩,z.property⟩

theorem center_map_le_diagonalNormalizer (K : Type) [Field K] :
    (Subgroup.center (MatrixGroup K)).map (MatrixGroup K).subtype ≤ diagonalNormalizer K := by
  rintro _ ⟨z,hz,rfl⟩
  exact center_mem_diagonalNormalizer K z hz

theorem envelope_bruhat_block_unique (K : Type) [Field K]
    (v w : List (Fin 6)) (b₁ b₂ : (Matrix GeckIndex GeckIndex K)ˣ)
    (hb₁ : b₁∈normalizerEnvelope K) (hb₂ : b₂∈normalizerEnvelope K)
    (he : b₁*wordUnit A hs hp E6Base E6Index K v*b₂=wordUnit A hs hp E6Base E6Index K w) :
    wordBlockPermutation A hd hs hp ho v=wordBlockPermutation A hd hs hp ho w :=
  CFSGNormTwoCoordinateNormalizerEnvelope.envelope_bruhat_block_unique A hd hs hp ho K
    E6Signs E6_signs_square E6_signs_cartan (E6_normalizer_word_identity K) (by decide)
    v w b₁ b₂ hb₁ hb₂ he

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckEnvelopeBlocks
