import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotentRoots
import SymmetricSubgroupAsymptotics.CFSGQuadraticParameterCentralizer

/-! Every actual central element of the literal B-unipotent subgroup
centralizes each original short-root coefficient. The quadratic term is
separated by actual root words with parameters 1 and -1. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationShortArrays
variable {K : Type} [Field K]

theorem central_short_polynomial_commutes (s : ℕ)
    (z : unipotent K (s + 1)) (hz : z ∈ Subgroup.center (unipotent K (s + 1)))
    (i : Fin (s + 1)) (a : K) :
    (z.val.val : Mat K (s + 1)) *
        (1 + a • shortArray K (s + 1) (Sum.inl i) +
          a ^ 2 • shortSecond K (s + 1) (Sum.inl i)) =
      (1 + a • shortArray K (s + 1) (Sum.inl i) +
          a ^ 2 • shortSecond K (s + 1) (Sum.inl i)) * (z.val.val : Mat K (s + 1)) := by
  have h := congrArg (fun u : unipotent K (s + 1) => (u.val.val : Mat K (s + 1)))
    (Subgroup.mem_center_iff.mp hz (shortInU K s i a)).symm
  change (z.val.val : Mat K (s + 1)) * (shortUnit K (s + 1) (Sum.inl i) a : Mat K (s + 1)) =
    (shortUnit K (s + 1) (Sum.inl i) a : Mat K (s + 1)) * (z.val.val : Mat K (s + 1)) at h
  exact h

theorem central_short_linear_commutes (h2 : (2 : K) ≠ 0) (s : ℕ)
    (z : unipotent K (s + 1)) (hz : z ∈ Subgroup.center (unipotent K (s + 1)))
    (i : Fin (s + 1)) :
    (z.val.val : Mat K (s + 1)) * shortArray K (s + 1) (Sum.inl i) =
      shortArray K (s + 1) (Sum.inl i) * (z.val.val : Mat K (s + 1)) := by
  apply CFSGQuadraticParameterCentralizer.linear_coefficient h2 _ _ _
  · simpa only [one_smul, one_pow] using central_short_polynomial_commutes s z hz i 1
  · simpa only [neg_one_smul, neg_one_sq, one_smul, sub_eq_add_neg] using
      central_short_polynomial_commutes s z hz i (-1)

theorem central_short_quadratic_commutes (h2 : (2 : K) ≠ 0) (s : ℕ)
    (z : unipotent K (s + 1)) (hz : z ∈ Subgroup.center (unipotent K (s + 1)))
    (i : Fin (s + 1)) :
    (z.val.val : Mat K (s + 1)) * shortSecond K (s + 1) (Sum.inl i) =
      shortSecond K (s + 1) (Sum.inl i) * (z.val.val : Mat K (s + 1)) := by
  apply CFSGQuadraticParameterCentralizer.quadratic_coefficient h2 _ _ _
  · simpa only [one_smul, one_pow] using central_short_polynomial_commutes s z hz i 1
  · simpa only [neg_one_smul, neg_one_sq, one_smul, sub_eq_add_neg] using
      central_short_polynomial_commutes s z hz i (-1)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
