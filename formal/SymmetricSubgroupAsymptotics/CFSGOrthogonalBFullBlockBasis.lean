import SymmetricSubgroupAsymptotics.CFSGOrthogonalBFullBlockCoordinates
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Exact reconstruction of the whole rational natural B Lie algebra
from its literal full coordinates. This is target-side linear algebra;
it does not identify the original Serre source with that algebra. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBFullBlockBasis
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBOriginalRootCandidates
open CFSGOrthogonalBFullMatrixCoordinates CFSGOrthogonalBFullBlockCoordinates
variable (r : ℕ)
local instance : DecidableEq (BasisIndex r) := Classical.decEq _

theorem combination_coordinates (a : BasisIndex r → ℚ) :
    coordinates ℚ r (Fintype.linearCombination ℚ (matrix ℚ r) a) = a := by
  rw [Fintype.linearCombination_apply, map_sum]
  simp only [map_smul, coordinates_matrix]
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem combination_mem (a : BasisIndex r → ℚ) :
    Block ℚ r (Fintype.linearCombination ℚ (matrix ℚ r) a) := by
  apply (block_iff_mem_orthogonal r _).mpr
  rw [Fintype.linearCombination_apply]
  apply (skewAdjointMatricesLieSubalgebra (gram ℚ r)).sum_mem
  intro j hj
  exact (skewAdjointMatricesLieSubalgebra (gram ℚ r)).smul_mem (a j)
    ((block_iff_mem_orthogonal r _).mp (matrix_mem ℚ r j))

theorem reconstruction (M : Mat ℚ r) (hM : Block ℚ r M) :
    Fintype.linearCombination ℚ (matrix ℚ r) (coordinates ℚ r M) = M := by
  apply coordinates_injective ℚ r _ M (combination_mem r _) hM
  exact combination_coordinates r _

theorem lie_mem (M N : Mat ℚ r) (hM : Block ℚ r M) (hN : Block ℚ r N) :
    Block ℚ r ⁅M, N⁆ :=
  (block_iff_mem_orthogonal r _).mpr
    ((skewAdjointMatricesLieSubalgebra (gram ℚ r)).lie_mem
      ((block_iff_mem_orthogonal r _).mp hM) ((block_iff_mem_orthogonal r _).mp hN))

theorem bracket_table (i j : BasisIndex r) :
    ⁅matrix ℚ r i, matrix ℚ r j⁆ =
      Fintype.linearCombination ℚ (matrix ℚ r)
        (coordinates ℚ r ⁅matrix ℚ r i, matrix ℚ r j⁆) :=
  (reconstruction r _ (lie_mem r _ _ (matrix_mem ℚ r i) (matrix_mem ℚ r j))).symm

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBFullBlockBasis
