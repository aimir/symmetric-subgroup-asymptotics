import SymmetricSubgroupAsymptotics.CFSGTrialityGeckNormalizerEnvelope
import SymmetricSubgroupAsymptotics.CFSGGradedDiagonalOppositeIntersection
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOppositeIntersection
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeight

/-! The enlarged actual normalizer envelope, without identifying its
diagonal subgroup with the literal torus, still meets the negative
unipotent group trivially and has unique positive/diagonal factors. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckEnvelopeOppositeIntersection
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckPositiveTwist CFSGTrialityGeckNormalizerEnvelope
open CFSGNormTwoGeckOppositeIntersection CFSGNormTwoCoordinateHeight
open CFSGNormTwoGeckHeightSupport CFSGGradedDiagonalOppositeIntersection

theorem envelope_negative_disjoint (K : Type) [Field K] :
    Disjoint (normalizerEnvelope K) (Negative K) := by
  apply envelope_disjoint_opposite
    (weight (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base coordinateHeight)
    (normalizerEnvelope K) (Positive K) (diagonalNormalizer K) (Negative K)
  · exact positive_le_strict (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index coordinateHeight
      (simple_height (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)) K
  · exact negative_le_strict_opposite (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index coordinateHeight
      (simple_height (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)) K
  · intro d hd
    exact ⟨Matrix.diag (d : Matrix GeckIndex GeckIndex K),
      (diagonalNormalizer_isDiag K d hd).diagonal_diag.symm⟩
  · intro b hb
    obtain ⟨u, hu, d, hd, _, he⟩ := normalizer_envelope_factor K b hb
    exact ⟨u, hu, d, hd, he⟩

theorem positive_diagonalNormalizer_disjoint (K : Type) [Field K] :
    Disjoint (Positive K) (diagonalNormalizer K) := by
  apply Subgroup.disjoint_def.mpr
  intro u hu hd
  apply strict_diagonal_eq_one
    (weight (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base coordinateHeight) u
  · exact positive_le_strict (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index coordinateHeight
      (simple_height (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)) K hu
  · exact ⟨Matrix.diag (u : Matrix GeckIndex GeckIndex K),
      (diagonalNormalizer_isDiag K u hd).diagonal_diag.symm⟩

theorem positive_diagonalNormalizer_factors_injective (K : Type) [Field K] :
    Function.Injective (fun p : Positive K × diagonalNormalizer K =>
      (p.1.val : (Matrix GeckIndex GeckIndex K)ˣ) * p.2.val) :=
  Subgroup.mul_injective_of_disjoint (positive_diagonalNormalizer_disjoint K)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckEnvelopeOppositeIntersection
