import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootComponents
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexNormalizerIntersection
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPartialFlagUpper

/-! The genuine component parity excludes the remaining last-plane
swap in the SAME actual D group, in every characteristic. Thus its
literal U-normalizer is triangular. No full isometry-group recognition
or characteristic-two determinant shortcut is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexComponentNormalizer
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexUnipotent
open CFSGOrthogonalDIndexPositiveSpace CFSGOrthogonalDIndexRootComponents
open CFSGOrthogonalDIndexNormalizerIntersection CFSGOrthogonalDIndexMiddlePlane
open CFSGOrthogonalDIndexSingularComponents CFSGOrthogonalDIndexPartialFlagUpper
variable (K : Type) [Field K]

theorem normalizer_middle_lower_zero (s : ℕ)
    (A : elementaryRootGroup K (s + 4))
    (hA : A ∈ Subgroup.normalizer
      (unipotent K (s + 4) : Set (elementaryRootGroup K (s + 4)))) :
    (A.val : Mat K (s + 4)) (Sum.inr (lastIndex s))
      (Sum.inl (lastIndex s)) = 0 := by
  by_contra hcross
  have hd := normalizer_positive_intersection_finrank K s A hA hcross
  have he := elementary_even_distance K s A
  change Even ((s + 4) - Module.finrank K ↥(positiveSpace K (s + 4) ⊓
    (positiveSpace K (s + 4)).map (naturalLinearHom K (s + 4) A).toLinearMap)) at he
  rw [hd] at he
  obtain ⟨k, hk⟩ := he
  omega

theorem normalizer_triangular (s : ℕ)
    (A : elementaryRootGroup K (s + 4))
    (hA : A ∈ Subgroup.normalizer
      (unipotent K (s + 4) : Set (elementaryRootGroup K (s + 4)))) :
    (A.val : Mat K (s + 4)).BlockTriangular (flagEquiv (s + 4)) :=
  normalizer_upper_of_middle_zero K s A hA (normalizer_middle_lower_zero K s A hA)

theorem normalizer_le_borel (s : ℕ) :
    Subgroup.normalizer (unipotent K (s + 4) : Set (elementaryRootGroup K (s + 4))) ≤
      borel K (s + 4) := by
  intro A hA
  exact normalizer_triangular K s A hA

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexComponentNormalizer
