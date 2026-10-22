import SymmetricSubgroupAsymptotics.CFSGSquareZeroRootProducts
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicRootLines
import SymmetricSubgroupAsymptotics.CFSGMatrixConjugateDisplacement

/-! Intrinsic commuting/root-product tests constrain the SAME original
natural displacements. In odd characteristic, two commuting long roots
whose product is a long root have zero mixed displacement product.
This does not yet assert the converse polar-line adjacency theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent CFSGSquareZeroRootProducts
variable {K : Type} [Field K] [Finite K]

theorem highestRoot_displacement_squareZero (h2 : (2 : K) ≠ 0) (s : ℕ) (a : K) :
    (((highestRoot s a).val : Mat K (s + 3)) - 1) ^ 2 = 0 := by
  rw [highestRoot_val h2, add_sub_cancel_left]
  change (a • highestRootCoefficient (K := K) s) ^ 2 = 0
  rw [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul,
    highestRootCoefficient_square, smul_zero]

theorem longRoot_displacement_squareZero (h2 : (2 : K) ≠ 0) (s : ℕ)
    (x : elementaryRootGroup K (s + 3)) (hx : IsLongRootElement s x) :
    ((x.val : Mat K (s + 3)) - 1) ^ 2 = 0 := by
  obtain ⟨g, a, rfl⟩ := hx
  change (((g.val * (highestRoot s a).val * g.val⁻¹ : (Mat K (s + 3))ˣ) : Mat K (s + 3)) - 1) ^ 2 = 0
  rw [CFSGMatrixConjugateDisplacement.conjugate_sub_one]
  exact unit_conjugate_squareZero g.val _ (highestRoot_displacement_squareZero h2 s a)

theorem commuting_longRoot_product_mixed_zero (h2 : (2 : K) ≠ 0) (s : ℕ)
    (x y : elementaryRootGroup K (s + 3)) (hx : IsLongRootElement s x)
    (hy : IsLongRootElement s y) (hc : Commute x y) (hxy : IsLongRootElement s (x * y)) :
    ((x.val : Mat K (s + 3)) - 1) * ((y.val : Mat K (s + 3)) - 1) = 0 := by
  have hcu : Commute x.val y.val := congrArg Subtype.val hc.eq
  have he := commuting_units_displacement_square x.val y.val
    (longRoot_displacement_squareZero h2 s x hx)
    (longRoot_displacement_squareZero h2 s y hy) hcu
  have hzero : 2 • (((x.val : Mat K (s + 3)) - 1) * ((y.val : Mat K (s + 3)) - 1)) = 0 := by
    exact he.symm.trans (longRoot_displacement_squareZero h2 s (x * y) hxy)
  have hscalar : (2 : K) •
      (((x.val : Mat K (s + 3)) - 1) * ((y.val : Mat K (s + 3)) - 1)) = 0 := by
    simpa only [two_smul, two_nsmul] using hzero
  exact (smul_eq_zero.mp hscalar).resolve_left h2

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots
