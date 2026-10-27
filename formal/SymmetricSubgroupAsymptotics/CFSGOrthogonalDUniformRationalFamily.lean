import SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformRootCoordinates
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDRationalCartanCoordinates

/-! Complete rational natural D family and its genuine coefficient
extractor. Cartan half-sums are used only over Q; no ambient integral
coordinate splitting or source faithfulness is asserted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformRationalFamily
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDOriginalRootCandidates
variable (r : ℕ) (hr : 4 ≤ r)
local instance : DecidableEq (BasisIndex r) := Classical.decEq _

def diagonal : Mat ℚ r→ₗ[ℚ](Fin r→ℚ) where
  toFun M i:=M (.inl i) (.inl i)
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

def matrix : BasisIndex r→Mat ℚ r
  | .inl i=>cartan ℚ r i
  | .inr j=>CFSGOrthogonalDUniformRootCoordinates.matrix ℚ r j

def coordinates : Mat ℚ r→ₗ[ℚ](BasisIndex r→ℚ) :=
  LinearMap.pi (fun
    | .inl i=>(LinearMap.proj i).comp
        ((CFSGOrthogonalDRationalCartanCoordinates.coordinates r hr).comp (diagonal r))
    | .inr j=>(LinearMap.proj j).comp
        (CFSGOrthogonalDUniformRootCoordinates.coordinates ℚ r))

private theorem pair_ne (ij : Pair r) : ij.val.1≠ij.val.2 := by
  intro h
  have hv:=congrArg Fin.val h
  have hp:=ij.property
  omega

theorem root_diagonal_zero (j : Bool×RootIndex r) :
    diagonal r (CFSGOrthogonalDUniformRootCoordinates.matrix ℚ r j)=0 := by
  have hd : (CFSGOrthogonalDUniformRootCoordinates.matrix ℚ r j).diag=0 := by
    rcases j with ⟨neg,ij | ij⟩ <;> cases neg <;>
      simp [CFSGOrthogonalDUniformRootCoordinates.matrix,
        CFSGOrthogonalDUniformRootMatrixArithmetic.difference,
        CFSGOrthogonalDUniformRootMatrixArithmetic.sumRoot,
        Matrix.transpose_sub,Matrix.transpose_single,Matrix.diag_sub,
        Matrix.diag_single_of_ne,pair_ne r ij,Ne.symm (pair_ne r ij)]
  funext i
  exact congrFun hd (.inl i)

include hr in
theorem cartan_root_coordinates_zero (i : Fin r) :
    CFSGOrthogonalDUniformRootCoordinates.coordinates ℚ r (cartan ℚ r i)=0 := by
  obtain ⟨d,hd⟩:=cartan_isDiagonal ℚ r hr i
  funext j
  rcases j with ⟨neg,ij | ij⟩ <;> cases neg <;>
    simp [CFSGOrthogonalDUniformRootCoordinates.coordinates,
      CFSGOrthogonalDUniformRootCoordinates.entry,hd,Matrix.diagonal_apply,
      pair_ne r ij,Ne.symm (pair_ne r ij)]

theorem coordinates_matrix (j : BasisIndex r) :
    coordinates r hr (matrix r j)=Pi.single j 1 := by
  funext k
  rcases j with i | j <;> rcases k with a | k
  · change CFSGOrthogonalDRationalCartanCoordinates.coordinates r hr
      (fun b=>cartan ℚ r i (.inl b) (.inl b)) a=_
    rw [CFSGOrthogonalDRationalCartanCoordinates.coordinates_cartan]
    simp [Pi.single_apply]
  · change CFSGOrthogonalDUniformRootCoordinates.coordinates ℚ r (cartan ℚ r i) k=_
    rw [cartan_root_coordinates_zero r hr]
    simp [Pi.single_apply]
  · change CFSGOrthogonalDRationalCartanCoordinates.coordinates r hr
      (diagonal r (CFSGOrthogonalDUniformRootCoordinates.matrix ℚ r j)) a=_
    rw [root_diagonal_zero,map_zero]
    simp [Pi.single_apply]
  · change CFSGOrthogonalDUniformRootCoordinates.coordinates ℚ r
      (CFSGOrthogonalDUniformRootCoordinates.matrix ℚ r j) k=_
    rw [CFSGOrthogonalDUniformRootCoordinates.coordinates_matrix]
    simp [Pi.single_apply]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformRationalFamily
