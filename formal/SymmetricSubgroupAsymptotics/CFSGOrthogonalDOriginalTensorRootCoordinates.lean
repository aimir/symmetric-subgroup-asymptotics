import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalIntegralBasis
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalScaledRealization

/-! Every ambient-zero vector in the SAME original tensor Space has zero
root coordinates, and is therefore a literal Cartan combination. This
holds in characteristic two as well; no ambient injection is asserted. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalTensorRootCoordinates
open CFSG.Models.Chevalley CFSGOrthogonalDSerreMatrices
open CFSGOrthogonalDOriginalRootCandidates CFSGOrthogonalDOriginalIntegralBasis
variable (r : ℕ) (hr : 4 ≤ r)

def matrixOver (K : Type*) [CommRing K] : BasisIndex r→Mat K r
  | .inl i=>cartan K r i
  | .inr j=>CFSGOrthogonalDUniformRootCoordinates.matrix K r j

theorem integerMatrix_map (K : Type*) [CommRing K] (j : BasisIndex r) :
    (Int.castRingHom K).mapMatrix
      (CFSGOrthogonalDOriginalScaledRealization.integerMatrix r j)=matrixOver r K j := by
  rcases j with i | ⟨neg,ij | ij⟩
  · exact map_cartan ℤ r (Int.castRingHom K) i
  all_goals
    cases neg <;> ext x y <;>
      simp [CFSGOrthogonalDOriginalScaledRealization.integerMatrix,matrixOver,
        CFSGOrthogonalDUniformRootCoordinates.matrix,
        CFSGOrthogonalDUniformRootMatrixArithmetic.difference,
        CFSGOrthogonalDUniformRootMatrixArithmetic.sumRoot,RingHom.mapMatrix,
        Matrix.map_apply,Matrix.transpose_apply,Matrix.sub_apply,Matrix.single_apply,and_comm]

theorem tensorBasis_image (K : Type) [Field K] (j : BasisIndex r) :
    orthogonalBaseChange K r hr (tensorBasis r hr K j)=matrixOver r K j := by
  rw [tensorBasis_apply]
  change CFSGSerreSquareZeroMatrix.baseChange (realizationData r hr) K
    ((1 : K) ⊗ₜ[ℤ] vector r hr j)=_
  rw [CFSGSerreSquareZeroMatrix.baseChange_tmul,one_smul,
    CFSGOrthogonalDOriginalScaledRealization.vector_image,integerMatrix_map]

include hr in
theorem cartan_root_coordinates (K : Type*) [CommRing K] (i : Fin r) :
    CFSGOrthogonalDUniformRootCoordinates.coordinates K r (cartan K r i)=0 := by
  obtain ⟨d,hd⟩:=cartan_isDiagonal K r hr i
  funext j
  change cartan K r i (CFSGOrthogonalDUniformRootCoordinates.entry r j).1
    (CFSGOrthogonalDUniformRootCoordinates.entry r j).2=0
  rw [hd]
  rcases j with ⟨neg,ij | ij⟩
  all_goals
    have hne : ij.val.1≠ij.val.2 := fun h=>ij.property.ne (congrArg Fin.val h)
    cases neg <;>
      simp [CFSGOrthogonalDUniformRootCoordinates.entry,Matrix.diagonal_apply,hne,Ne.symm hne]

include hr in
theorem matrixOver_root_coordinates (K : Type*) [CommRing K] (j : BasisIndex r) :
    CFSGOrthogonalDUniformRootCoordinates.coordinates K r (matrixOver r K j)=
      match j with
      | .inl _=>0
      | .inr k=>Pi.single k 1 := by
  cases j with
  | inl i => exact cartan_root_coordinates r hr K i
  | inr j =>
    change CFSGOrthogonalDUniformRootCoordinates.coordinates K r
      (CFSGOrthogonalDUniformRootCoordinates.matrix K r j) = Pi.single j 1
    have h := CFSGOrthogonalDUniformRootCoordinates.coordinates_matrix K r j
    refine h.trans ?_
    funext k
    by_cases hk : k = j <;> simp [Pi.single_apply,hk]

theorem root_coordinate (K : Type) [Field K] (x : Space (CartanMatrix.D r) K)
    (j : Bool×RootIndex r) :
    CFSGOrthogonalDUniformRootCoordinates.coordinates K r
      (orthogonalBaseChange K r hr x) j=(tensorBasis r hr K).repr x (.inr j) := by
  have h:=congrArg (orthogonalBaseChange K r hr) (tensor_expansion r hr K x)
  simp only [map_sum,map_smul,←tensorBasis_apply r hr K,tensorBasis_image] at h
  have hc:=congrArg (CFSGOrthogonalDUniformRootCoordinates.coordinates K r) h
  simp only [Fintype.sum_sum_type] at hc
  simp only [map_add,map_sum,map_smul,matrixOver_root_coordinates r hr K,
    smul_zero,Finset.sum_const_zero,zero_add] at hc
  have hj:=congrFun hc j
  simpa [Finset.sum_apply,Pi.single_apply] using hj.symm

theorem kernel_eq_cartan_combination (K : Type) [Field K]
    (x : Space (CartanMatrix.D r) K) (hx : orthogonalBaseChange K r hr x=0) :
    x=∑ i : Fin r,(tensorBasis r hr K).repr x (.inl i) •
      ((1 : K) ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator (CartanMatrix.D r) (.H i)) := by
  have hz (j : Bool×RootIndex r) : (tensorBasis r hr K).repr x (.inr j)=0 := by
    rw [←root_coordinate r hr K x j,hx,map_zero]
    rfl
  have h:=tensor_expansion r hr K x
  simpa only [Fintype.sum_sum_type,hz,zero_smul,Finset.sum_const_zero,add_zero,vector] using h.symm

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalTensorRootCoordinates
