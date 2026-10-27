import SymmetricSubgroupAsymptotics.CFSGSymplecticUniformCorootWeights
import SymmetricSubgroupAsymptotics.FiniteLieFamilyCoefficientJacobi

/-! Genuine mixed coefficients for ALL positive-root source induction
rows, obtained from natural matrix Jacobi and the already-derived whole
positive raising/lowering tables. No row certificate is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticPositiveMixedCoefficients
open CFSGSymplecticSerreMatrices CFSGSymplecticUniformPositiveProfile
open CFSGSymplecticUniformPositiveTables CFSGSymplecticUniformCorootWeights
variable (r : ℕ)

theorem mixed_coefficients (i a : Fin r) (j : PositiveIndex r) (hj : 0 < height r j) :
    (if a=i then (-weight r a j) • Pi.single j 1 else 0)+
      (∑ l,lowering r a j l • raising r i l)=
        Fintype.linearCombination ℚ (lowering r a) (raising r i j) := by
  have hEF : ∀ a i : Fin r,⁅negative ℚ r a,positive ℚ r i⁆=
      if a=i then -cartan ℚ r a else 0 := by
    intro a i
    rw [←lie_skew (negative ℚ r a) (positive ℚ r i),EF]
    by_cases h : a=i
    · subst i; simp
    · simp [h,Ne.symm h]
  exact FiniteLieFamilyCoefficientJacobi.mixed_coefficients
    (positiveMatrix r) (positiveCoordinates r) (positive_coordinates_matrix r)
    (positive ℚ r) (negative ℚ r) (cartan ℚ r)
    (raising r) (lowering r) (weight r) (raising_table r) hEF
    (positive_matrix_weight r) i a j (lowering_table r a j hj)
    (fun l hl=>lowering_table r a l (by have hs:=raising_height r i j l hl; omega))

end SymmetricSubgroupAsymptotics.CFSGSymplecticPositiveMixedCoefficients
