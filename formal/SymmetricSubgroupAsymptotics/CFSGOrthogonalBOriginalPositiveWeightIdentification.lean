import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalPositivePrimitiveFamily
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUniformCorootWeights

/-! Source path weights equal the actual natural Cartan weights, using
only representation naturality and one proved primitive coordinate.
No global source spanning or realization injectivity is used. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalPositiveWeightIdentification
open CFSG.Models.Chevalley CFSGSerreSignedRootWeights
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBOriginalRootCandidates
open CFSGOrthogonalBFullMatrixCoordinates CFSGOrthogonalBUniformPositiveTables
open CFSGOrthogonalBOriginalPositiveSourceProfile CFSGOrthogonalBOriginalPositivePrimitiveFamily
variable (r : ℕ)

def rawWeight (a : Fin r) : PositiveIndex r → ℚ
  | .inl _ => 0
  | .inr j => rootWeight r a j

private theorem Hhalf_weight (a : Fin r) (j : ℕ) :
    ⁅coroot (CartanMatrix.B r).transpose false a,
      CFSGOrthogonalBOriginalRationalCartanTail.Hhalf r j⁆ = 0 := by
  by_cases h : j < r
  · rw [CFSGOrthogonalBOriginalRationalCartanTail.Hhalf, dif_pos h, lie_smul]
    have hc : ⁅coroot (CartanMatrix.B r).transpose false a,
        generator (CartanMatrix.B r).transpose (.H ⟨j, h⟩)⁆ = 0 :=
      coroots_commute (CartanMatrix.B r).transpose false a ⟨j, h⟩
    rw [hc, smul_zero]
  · rw [CFSGOrthogonalBOriginalRationalCartanTail.Hhalf, dif_neg h, lie_zero]

private theorem raw_source_weight (a : Fin r) (j : PositiveIndex r) :
    ⁅coroot (CartanMatrix.B r).transpose false a,
      CFSGOrthogonalBOriginalPositivePrimitiveFamily.source r j⁆ =
      rawWeight r a j • CFSGOrthogonalBOriginalPositivePrimitiveFamily.source r j := by
  cases j with
  | inl i =>
    simp only [CFSGOrthogonalBOriginalPositivePrimitiveFamily.source, rawWeight,
      zero_smul, CFSGOrthogonalBOriginalRationalCartanTail.tail, lie_sum]
    apply Finset.sum_eq_zero
    intro j hj
    exact Hhalf_weight r a _
  | inr j => exact CFSGOrthogonalBOriginalPositiveSourceProfile.root_weight r a j

theorem weight_eq (a : Fin r) (j : PositiveIndex r) :
    rawWeight r a j = CFSGOrthogonalBUniformCorootWeights.weight r a j := by
  have h := congrArg (rationalOrthogonalRepresentation r) (raw_source_weight r a j)
  have hH : rationalOrthogonalRepresentation r (coroot (CartanMatrix.B r).transpose false a) =
      cartan ℚ r a := rationalOrthogonalRepresentation_H r a
  simp only [LieHom.map_lie, map_smul, hH, source_image,
    CFSGOrthogonalBUniformCorootWeights.positive_matrix_weight] at h
  have hc := congrArg (fun M : Mat ℚ r => coordinates ℚ r M (fullIndex r j)) h
  simpa only [map_smul, positiveMatrix, coordinates_matrix, Pi.smul_apply,
    Pi.single_eq_same, smul_eq_mul, mul_one] using hc.symm

theorem source_weight (a : Fin r) (j : PositiveIndex r) :
    ⁅coroot (CartanMatrix.B r).transpose false a,
      CFSGOrthogonalBOriginalPositivePrimitiveFamily.source r j⁆ =
      CFSGOrthogonalBUniformCorootWeights.weight r a j •
        CFSGOrthogonalBOriginalPositivePrimitiveFamily.source r j := by
  rw [← weight_eq]
  exact raw_source_weight r a j

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalPositiveWeightIdentification
