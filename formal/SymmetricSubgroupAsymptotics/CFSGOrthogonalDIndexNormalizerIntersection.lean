import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexMiddlePlane
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveSpace
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPrefixDimension

/-! If an actual U-normalizer element has nonzero lower entry in the
last plane, its positive-space intersection is exactly the actual
prefix of dimension r-1. Thus the final-pair swap has odd component
distance; no name or classical-group identification excludes it. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexNormalizerIntersection
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexUnipotent
open CFSGOrthogonalDIndexPrefixNormalizer CFSGOrthogonalDIndexPrefixDimension
open CFSGOrthogonalDIndexMiddlePlane CFSGOrthogonalDIndexPositiveSpace
open CFSGMatrixFlagNormalizer
variable (K : Type) [Field K]

theorem lastPrefix_le_positive (s : ℕ) :
    flagPrefix (K := K) (flagEquiv (s + 4)) (s + 3) ≤ positiveSpace K (s + 4) := by
  intro x hx j
  exact hx (Sum.inr j) (by change s + 3 ≤ s + 4 + (Fin.rev j).val; omega)

theorem positive_mem_lastPrefix_iff (s : ℕ) (x : Index (s + 4) → K)
    (hx : x ∈ positiveSpace K (s + 4)) :
    x ∈ flagPrefix (K := K) (flagEquiv (s + 4)) (s + 3) ↔
      x (Sum.inl (lastIndex s)) = 0 := by
  constructor
  · intro h
    exact h (Sum.inl (lastIndex s)) (by change s + 3 ≤ s + 3; exact le_rfl)
  · intro h i hi
    cases i with
    | inl j =>
      have he : j = lastIndex s := by
        apply Fin.ext
        change j.val = s + 3
        change s + 3 ≤ j.val at hi
        have hb := j.isLt
        omega
      subst j
      exact h
    | inr j => exact hx j

theorem last_negative_mulVec (s : ℕ) (A : elementaryRootGroup K (s + 4))
    (hA : A ∈ Subgroup.normalizer
      (unipotent K (s + 4) : Set (elementaryRootGroup K (s + 4))))
    (x : Index (s + 4) → K) (hx : x ∈ positiveSpace K (s + 4)) :
    ((A.val : Mat K (s + 4)) *ᵥ x) (Sum.inr (lastIndex s)) =
      (A.val : Mat K (s + 4)) (Sum.inr (lastIndex s)) (Sum.inl (lastIndex s)) *
        x (Sum.inl (lastIndex s)) := by
  change (∑ j : Index (s + 4), (A.val : Mat K (s + 4))
    (Sum.inr (lastIndex s)) j * x j) = _
  rw [Fintype.sum_sum_type]
  have hp : (∑ j : Fin (s + 4), (A.val : Mat K (s + 4))
      (Sum.inr (lastIndex s)) (Sum.inl j) * x (Sum.inl j)) =
      (A.val : Mat K (s + 4)) (Sum.inr (lastIndex s)) (Sum.inl (lastIndex s)) *
        x (Sum.inl (lastIndex s)) := by
    apply Finset.sum_eq_single (lastIndex s)
    · intro j _ hj
      have hlt : j.val < s + 3 := by
        have hb := j.isLt
        have hn : j.val ≠ s + 3 := fun h => hj (Fin.ext h)
        omega
      have hz := normalizer_positive_column_zero K s A hA j (by omega)
        (Sum.inr (lastIndex s)) (by
          change j.val < s + 4 + (Fin.rev (lastIndex s)).val
          omega)
      rw [hz, zero_mul]
    · intro h
      exact False.elim (h (Finset.mem_univ _))
  have hn : (∑ j : Fin (s + 4), (A.val : Mat K (s + 4))
      (Sum.inr (lastIndex s)) (Sum.inr j) * x (Sum.inr j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [hx j, mul_zero]
  rw [hp, hn, add_zero]

theorem normalizer_positive_intersection_prefix (s : ℕ)
    (A : elementaryRootGroup K (s + 4))
    (hA : A ∈ Subgroup.normalizer
      (unipotent K (s + 4) : Set (elementaryRootGroup K (s + 4))))
    (hcross : (A.val : Mat K (s + 4)) (Sum.inr (lastIndex s))
      (Sum.inl (lastIndex s)) ≠ 0) :
    positiveSpace K (s + 4) ⊓ (positiveSpace K (s + 4)).map
      (naturalLinearHom K (s + 4) A).toLinearMap =
        flagPrefix (K := K) (flagEquiv (s + 4)) (s + 3) := by
  ext x
  constructor
  · rintro ⟨hx, y, hy, he⟩
    change (A.val : Mat K (s + 4)) *ᵥ y = x at he
    have hp := last_negative_mulVec K s A hA y hy
    rw [he, hx (lastIndex s)] at hp
    have hy0 : y (Sum.inl (lastIndex s)) = 0 :=
      (mul_eq_zero.mp hp.symm).resolve_left hcross
    have hyp := (positive_mem_lastPrefix_iff K s y hy).mpr hy0
    have h := normalizer_preserves_positivePrefix K s A hA (s + 3) (by omega) y hyp
    rw [he] at h
    exact h
  · intro hx
    have hAi : A⁻¹ ∈ Subgroup.normalizer
        (unipotent K (s + 4) : Set (elementaryRootGroup K (s + 4))) :=
      (Subgroup.normalizer _).inv_mem hA
    let y := naturalLinearHom K (s + 4) A⁻¹ x
    have hyp : y ∈ flagPrefix (K := K) (flagEquiv (s + 4)) (s + 3) :=
      normalizer_preserves_positivePrefix K s A⁻¹ hAi (s + 3) (by omega) x hx
    refine ⟨lastPrefix_le_positive K s hx, y, lastPrefix_le_positive K s hyp, ?_⟩
    change naturalLinearHom K (s + 4) A (naturalLinearHom K (s + 4) A⁻¹ x) = x
    rw [map_inv]
    exact (naturalLinearHom K (s + 4) A).apply_symm_apply x

theorem normalizer_positive_intersection_finrank (s : ℕ)
    (A : elementaryRootGroup K (s + 4))
    (hA : A ∈ Subgroup.normalizer
      (unipotent K (s + 4) : Set (elementaryRootGroup K (s + 4))))
    (hcross : (A.val : Mat K (s + 4)) (Sum.inr (lastIndex s))
      (Sum.inl (lastIndex s)) ≠ 0) :
    Module.finrank K ↥(positiveSpace K (s + 4) ⊓ (positiveSpace K (s + 4)).map
      (naturalLinearHom K (s + 4) A).toLinearMap) = s + 3 := by
  rw [normalizer_positive_intersection_prefix K s A hA hcross]
  exact flagPrefix_finrank K (flagEquiv (s + 4)) (s + 3) (by omega)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexNormalizerIntersection
