import SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalPositiveSourceWeights
import SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalPrimitiveFamily
import SymmetricSubgroupAsymptotics.CFSGSymplecticUniformCorootWeights

/-! Original source path weights equal the literal natural Cartan weights.
Only representation naturality and one primitive matrix entry are used;
no realization injectivity or source spanning is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalPositiveWeightIdentification
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreSignedRootWeights
open CFSGSymplecticSerreMatrices CFSGSymplecticOriginalRootCandidates
open CFSGSymplecticUniformRootCoordinates CFSGSymplecticUniformPositiveProfile
open CFSGSymplecticUniformPositiveTables CFSGSymplecticOriginalPrimitiveFamily
variable (r : ℕ)

private theorem cast_matrix (j : BasisIndex r) :
    intMatrixLinearMap r (matrix ℤ r j)=matrix ℚ r j := by
  ext x y
  rcases j with i | ⟨neg,j⟩
  · simp [matrix,intMatrixLinearMap,Matrix.map_apply,Matrix.single_apply]
  · cases neg <;> rcases j with ij | (i | ij) <;>
      simp [matrix,intMatrixLinearMap,Matrix.map_apply,Matrix.single_apply]

theorem source_image (j : PositiveIndex r) :
    rationalSymplecticRepresentation r
      (CFSGSymplecticOriginalPositiveSourceWeights.source r j)=positiveMatrix r j := by
  have h:=integralSymplecticRepresentation_cast r (primitiveVector r (fullIndex r j))
  rw [primitiveVector_image,cast_matrix] at h
  cases j <;> exact h.symm

theorem weight_eq (a : Fin r) (j : PositiveIndex r) :
    CFSGSymplecticOriginalPositiveSourceWeights.weight r a j =
      CFSGSymplecticUniformCorootWeights.weight r a j := by
  have h:=congrArg (rationalSymplecticRepresentation r)
    (CFSGSymplecticOriginalPositiveSourceWeights.source_weight r a j)
  have hH : rationalSymplecticRepresentation r
      (coroot (CartanMatrix.C r).transpose false a)=cartan ℚ r a := by
    exact rationalSymplecticRepresentation_H r a
  simp only [LieHom.map_lie,map_smul,hH,source_image,
    CFSGSymplecticUniformCorootWeights.positive_matrix_weight] at h
  have hc:=congrArg (fun M : Mat ℚ r => coordinates ℚ r M (fullIndex r j)) h
  simpa only [map_smul,positiveMatrix,coordinates_matrix,Pi.smul_apply,
    Pi.single_eq_same,smul_eq_mul,mul_one] using hc.symm

theorem source_weight (a : Fin r) (j : PositiveIndex r) :
    ⁅coroot (CartanMatrix.C r).transpose false a,
      CFSGSymplecticOriginalPositiveSourceWeights.source r j⁆ =
      CFSGSymplecticUniformCorootWeights.weight r a j •
        CFSGSymplecticOriginalPositiveSourceWeights.source r j := by
  rw [←weight_eq]
  exact CFSGSymplecticOriginalPositiveSourceWeights.source_weight r a j

end SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalPositiveWeightIdentification
