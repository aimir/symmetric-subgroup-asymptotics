import SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformCorootWeights
import SymmetricSubgroupAsymptotics.FiniteLieFamilyCoefficientJacobi

/-! Genuine mixed coefficients for ALL positive-root source induction
rows, obtained from natural matrix Jacobi and the already-derived whole
positive raising/lowering tables. No row certificate is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDPositiveMixedCoefficients
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDUniformPositiveProfile
open CFSGOrthogonalDUniformPositiveTables CFSGOrthogonalDUniformCorootWeights
variable (r : ℕ) (hr : 4 ≤ r)

theorem mixed_coefficients (i a : Fin r) (j : PositiveIndex r) (hj : 0 < height r j) :
    (if a=i then (-weight r a j) • Pi.single j 1 else 0)+
      (∑ l,lowering r hr a j l • raising r hr i l)=
        Fintype.linearCombination ℚ (lowering r hr a) (raising r hr i j) := by
  have hEF : ∀ a i : Fin r,⁅negative ℚ r a,positive ℚ r i⁆=
      if a=i then -cartan ℚ r a else 0 := by
    intro a i
    rw [←lie_skew (negative ℚ r a) (positive ℚ r i),EF ℚ r hr]
    by_cases h : a=i
    · subst i; simp
    · simp [h,Ne.symm h]
  exact FiniteLieFamilyCoefficientJacobi.mixed_coefficients
    (positiveMatrix r) (positiveCoordinates r hr) (positive_coordinates_matrix r hr)
    (positive ℚ r) (negative ℚ r) (cartan ℚ r)
    (raising r hr) (lowering r hr) (weight r) (raising_table r hr) hEF
    (positive_matrix_weight r hr) i a j (lowering_table r hr a j hj)
    (fun l hl=>lowering_table r hr a l (by have hs:=raising_height r hr i j l hl; omega))

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDPositiveMixedCoefficients
