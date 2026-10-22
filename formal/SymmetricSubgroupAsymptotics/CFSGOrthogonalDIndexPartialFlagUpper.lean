import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexMiddleAction

/-! The partial flag plus the actual lower entry of the final plane
recover full triangularity. The entry hypothesis is retained explicitly;
the odd-prime power theorem supplies it in its genuine application. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPartialFlagUpper
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexUnipotent
open CFSGOrthogonalDIndexPrefixNormalizer CFSGOrthogonalDIndexPrefixPerpendicular
open CFSGOrthogonalDIndexMiddlePlane CFSGOrthogonalDIndexMiddleAction
variable (K : Type) [Field K]

theorem normalizer_upper_of_middle_zero (s : ℕ)
    (A : elementaryRootGroup K (s + 4))
    (hA : A ∈ Subgroup.normalizer
      (unipotent K (s + 4) : Set (elementaryRootGroup K (s + 4))))
    (hmid : (A.val : Mat K (s + 4)) (Sum.inr (lastIndex s))
      (Sum.inl (lastIndex s)) = 0) :
    (A.val : Mat K (s + 4)).BlockTriangular (flagEquiv (s + 4)) := by
  intro x y hxy
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      have hij : j.val < i.val := hxy
      exact normalizer_positive_column_zero K s A hA j
        (by have hb := i.isLt; omega) (Sum.inl i) hxy
    | inr j =>
      exact False.elim ((not_lt_of_gt (flag_pos_lt_neg (s + 4) i j)) hxy)
  | inr i =>
    cases y with
    | inl j =>
      by_cases hj : j = lastIndex s
      · subst j
        by_cases hi : i = lastIndex s
        · subst i
          exact hmid
        · have hilt : i.val < s + 3 := by
            have hb := i.isLt
            have hn : i.val ≠ s + 3 := fun h => hi (Fin.ext h)
            omega
          have hcol := normalizer_preserves_positivePerpendicular K s A hA (s + 3)
            (by omega) _ (middle_basis_perpendicular K s false)
          have hz := hcol i hilt
          change ((A.val : Mat K (s + 4)) *ᵥ Pi.single (Sum.inl (lastIndex s)) 1)
            (Sum.inr i) = 0 at hz
          rw [Matrix.mulVec_single_one] at hz
          exact hz
      · have hjlt : j.val < s + 3 := by
          have hb := j.isLt
          have hn : j.val ≠ s + 3 := fun h => hj (Fin.ext h)
          omega
        exact normalizer_positive_column_zero K s A hA j (by omega) (Sum.inr i) hxy
    | inr j =>
      have hrev : Fin.rev j < Fin.rev i := by
        change s + 4 + (Fin.rev j).val < s + 4 + (Fin.rev i).val at hxy
        change (Fin.rev j).val < (Fin.rev i).val
        omega
      have hij : i < j := Fin.rev_lt_rev.mp hrev
      have hv : Pi.single (Sum.inr j) (1 : K) ∈
          positivePerpendicular K (s + 4) j.val := by
        intro l hl
        have hlj : l ≠ j := by intro he; subst l; omega
        simp [Pi.single_apply, hlj, Ne.symm hlj]
      have hcol := normalizer_preserves_positivePerpendicular K s A hA j.val j.isLt _ hv
      have hz := hcol i hij
      change ((A.val : Mat K (s + 4)) *ᵥ Pi.single (Sum.inr j) 1) (Sum.inr i) = 0 at hz
      rw [Matrix.mulVec_single_one] at hz
      exact hz

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPartialFlagUpper
