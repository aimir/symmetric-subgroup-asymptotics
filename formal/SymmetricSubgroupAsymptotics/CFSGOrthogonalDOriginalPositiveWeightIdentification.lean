import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalPositiveSourceWeights
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalPositiveRootImages
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformCorootWeights

/-! Actual original D path weights are identified through one literal
nonzero matrix coordinate, without source faithfulness or spanning. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalPositiveWeightIdentification
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreSignedRootWeights
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDOriginalRootCandidates
open CFSGOrthogonalDUniformRationalFamily CFSGOrthogonalDUniformPositiveProfile
open CFSGOrthogonalDUniformPositiveTables CFSGOrthogonalDOriginalPositiveRootImages
variable (r : ℕ) (hr : 4 ≤ r)

theorem source_image (j : PositiveIndex r) :
    rationalOrthogonalRepresentation r hr
      (CFSGOrthogonalDOriginalPositiveSourceWeights.source r hr j)=positiveMatrix r j := by
  cases j with
  | inl i => exact rationalOrthogonalRepresentation_H r hr i
  | inr j =>
    change rationalOrthogonalRepresentation r hr (root r hr false j).val=
      positiveMatrix r (.inr j)
    have h:=CFSGSerreSquareZeroMatrix.integralRepresentation_cast
      (realizationData r hr) (root r hr false j)
    change (Int.castRingHom ℚ).mapMatrix
      (integralOrthogonalRepresentation r hr (root r hr false j))=
        rationalOrthogonalRepresentation r hr (root r hr false j).val at h
    rw [←h]
    cases j with
    | inl ij =>
      rw [root,difference_image]
      ext x y
      simp only [positiveMatrix,fullIndex,matrix,
        CFSGOrthogonalDUniformRootCoordinates.matrix,
        CFSGOrthogonalDUniformRootMatrixArithmetic.difference,
        map_sub]
      simp [RingHom.mapMatrix,Matrix.map_apply,Matrix.sub_apply,Matrix.single_apply]
    | inr ij =>
      rw [root,sum_image]
      ext x y
      simp only [positiveMatrix,fullIndex,matrix,
        CFSGOrthogonalDUniformRootCoordinates.matrix,
        CFSGOrthogonalDUniformRootMatrixArithmetic.sumRoot,
        map_sub]
      simp [RingHom.mapMatrix,Matrix.map_apply,Matrix.sub_apply,Matrix.single_apply]

theorem weight_eq (a : Fin r) (j : PositiveIndex r) :
    CFSGOrthogonalDOriginalPositiveSourceWeights.weight r hr a j=
      CFSGOrthogonalDUniformCorootWeights.weight r a j := by
  have h:=congrArg (rationalOrthogonalRepresentation r hr)
    (CFSGOrthogonalDOriginalPositiveSourceWeights.source_weight r hr a j)
  have hH : rationalOrthogonalRepresentation r hr
      (coroot (CartanMatrix.D r) false a)=cartan ℚ r a :=
    rationalOrthogonalRepresentation_H r hr a
  simp only [LieHom.map_lie,map_smul,hH,source_image,
    CFSGOrthogonalDUniformCorootWeights.positive_matrix_weight r hr] at h
  have hc:=congrArg (fun M : Mat ℚ r=>coordinates r hr M (fullIndex r j)) h
  simpa only [map_smul,positiveMatrix,coordinates_matrix,Pi.smul_apply,
    Pi.single_eq_same,smul_eq_mul,mul_one] using hc.symm

theorem source_weight (a : Fin r) (j : PositiveIndex r) :
    ⁅coroot (CartanMatrix.D r) false a,
      CFSGOrthogonalDOriginalPositiveSourceWeights.source r hr j⁆=
      CFSGOrthogonalDUniformCorootWeights.weight r a j •
        CFSGOrthogonalDOriginalPositiveSourceWeights.source r hr j := by
  rw [←weight_eq]
  exact CFSGOrthogonalDOriginalPositiveSourceWeights.source_weight r hr a j

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalPositiveWeightIdentification
