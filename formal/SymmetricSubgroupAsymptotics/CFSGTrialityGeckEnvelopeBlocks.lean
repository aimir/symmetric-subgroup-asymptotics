import SymmetricSubgroupAsymptotics.CFSGTrialityGeckNormalizerEnvelope
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckBruhatBlockUniqueness
import Mathlib.GroupTheory.Subgroup.Center

/-! The enlarged normalizer envelope is triangular for the SAME
separating root blocks. Central elementary-group elements belong to its
diagonal factor; no scalar-centre or torus-centre recognition is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckEnvelopeBlocks
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckNormalizerEnvelope CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckAmbientPositiveSylow
open CFSGTrialityGeckBruhatBlockUniqueness CFSGTrialityGeckWeylBlocks
open CFSGTrialityD4SeparatingWeight CFSGNormTwoGeckPositivePGroup
local instance : LinearOrder WeightBlock := blockOrder

theorem envelope_block_triangular (K : Type) [Field K]
    (g : (Matrix GeckIndex GeckIndex K)ˣ) (hg : g ∈ normalizerEnvelope K) :
    (g : Matrix GeckIndex GeckIndex K).BlockTriangular geckBlock := by
  obtain ⟨u,hu,d,_,hdiag,he⟩ := normalizer_envelope_factor K g hg
  rw [he,Units.val_mul]
  apply (positive_block_triangular K u hu).mul
  rw [←hdiag.diagonal_diag]
  exact Matrix.blockTriangular_diagonal _

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
    change rootGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K true ≤
        CFSGSerreQuadraticMatrix.canonicalElementaryGroup
          (CFSGNormTwoGeckIntegralRealization.realizationData (CartanMatrix.D 4)
            (CartanMatrix.D_transpose 4) D4_positive_definite Base Index) K
    rw [←positive_sup_negative (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K]
    exact le_sup_right
  exact ⟨⟨center_normalizes_subgroup (MatrixGroup K) (Positive K)
    (positive_le_matrixGroup K) z hz,
    center_normalizes_subgroup (MatrixGroup K) (Negative K) hV z hz⟩,z.property⟩

theorem center_map_le_diagonalNormalizer (K : Type) [Field K] :
    (Subgroup.center (MatrixGroup K)).map (MatrixGroup K).subtype ≤ diagonalNormalizer K := by
  rintro _ ⟨z,hz,rfl⟩
  exact center_mem_diagonalNormalizer K z hz

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckEnvelopeBlocks
