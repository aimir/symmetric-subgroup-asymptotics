import SymmetricSubgroupAsymptotics.CFSGSymplecticSignedPathImages
import SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalCartanTail
import SymmetricSubgroupAsymptotics.CFSGSymplecticUniformRootCoordinates

/-! The ACTUAL complete primitive source family: integral Cartan tails
and signed divided-power root paths. Every original generator belongs
to its span, and literal matrix coordinates give a Kronecker left inverse
on this family. First action closure remains a separate proof obligation. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalPrimitiveFamily
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSymplecticSerreMatrices
open CFSGSymplecticOriginalRootCandidates CFSGSymplecticOriginalPositiveRootImages
open CFSGSymplecticSignedPathImages CFSGSymplecticOriginalCartanTail
open CFSGSymplecticUniformRootCoordinates
variable (r : ℕ)
local instance : DecidableEq (BasisIndex r) := Classical.decEq _

def primitiveVector : BasisIndex r→Source r
  | .inl i => tail r i.val
  | .inr (neg,j) => root r neg j

def matrixCoordinates : Mat ℤ r→ₗ[ℤ](BasisIndex r→ℤ) := coordinates ℤ r

theorem primitiveVector_image (j : BasisIndex r) :
    integralSymplecticRepresentation r (primitiveVector r j)=matrix ℤ r j := by
  rcases j with i | ⟨neg,j⟩
  · rw [primitiveVector,tail_image]
    simp only [CFSGSymplecticOriginalCartanTail.diagonal,dif_pos i.isLt,matrix]
  · cases neg <;> rcases j with ij | (i | ij)
    · exact difference_image r ij
    · exact long_image r i
    · exact sum_image r ij
    · simpa only [matrix,CFSGSymplecticUniformRootMatrixArithmetic.difference,
        Matrix.transpose_sub,Matrix.transpose_single] using difference_negative_image r ij
    · simpa only [matrix,CFSGSymplecticUniformRootMatrixArithmetic.long,
        Matrix.transpose_single] using long_negative_image r i
    · simpa only [matrix,CFSGSymplecticUniformRootMatrixArithmetic.sumRoot,
        Matrix.transpose_add,Matrix.transpose_single] using sum_negative_image r ij

theorem primitive_coordinates (j : BasisIndex r) :
    matrixCoordinates r (integralSymplecticRepresentation r (primitiveVector r j))=
      Pi.single j 1 := by
  rw [primitiveVector_image]
  exact coordinates_matrix ℤ r j

private theorem cartan_mem (i : Fin r) :
    latticeGenerator (CartanMatrix.C r).transpose (.H i)∈
      Submodule.span ℤ (Set.range (primitiveVector r)) := by
  rw [generator_H_from_tails]
  apply Submodule.sub_mem
  · exact Submodule.subset_span ⟨.inl i,rfl⟩
  · by_cases hi : i.val+1<r
    · exact Submodule.subset_span ⟨.inl ⟨i.val+1,hi⟩,rfl⟩
    · have hz : r-(i.val+1)=0:=by omega
      simp only [tail,hz,Finset.range_zero,Finset.sum_empty]
      exact Submodule.zero_mem _

theorem original_generators_mem (g : CartanMatrix.Generators (Fin r)) :
    latticeGenerator (CartanMatrix.C r).transpose g∈
      Submodule.span ℤ (Set.range (primitiveVector r)) := by
  let S:=Submodule.span ℤ (Set.range (primitiveVector r))
  have hOld : ∀ j : BasisIndex r,vector r j∈S := by
    intro j
    cases j with
    | inl i => exact cartan_mem r i
    | inr z => exact Submodule.subset_span ⟨.inr z,rfl⟩
  have hle : Submodule.span ℤ (Set.range (fun j=>(vector r j).val))≤
      S.map (integralLattice (CartanMatrix.C r).transpose).subtype := by
    apply Submodule.span_le.mpr
    rintro x ⟨j,rfl⟩
    exact ⟨vector r j,hOld j,rfl⟩
  obtain ⟨x,hx,he⟩:=hle (generator_mem_span r g)
  have he' : x=latticeGenerator (CartanMatrix.C r).transpose g:=Subtype.ext he
  exact he' ▸ hx

end SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalPrimitiveFamily
