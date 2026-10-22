import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCharTwoRestriction

/-! Exact image of characteristic-two restriction: the actual C
elementary root subgroup. Surjectivity uses finite-field square roots on
the terminal parameters, not an unproved B/C model identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCharTwoRange
open Matrix CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationElements
open CFSGOrthogonalBGenerationCharTwoRestriction
variable (K : Type) [Field K] [CharP K 2]

theorem restriction_range_le (r : ℕ) :
    (naturalRestriction K r).range ≤ CFSGSymplecticSerreMatrices.elementaryRootGroup K r := by
  let S := (CFSGSymplecticSerreMatrices.elementaryRootGroup K r).comap (naturalRestriction K r)
  have hle : Subgroup.closure
      {u : elementaryRootGroup K r | ∃ neg i a, u = rootElement K r neg i a} ≤ S := by
    apply (Subgroup.closure_le S).mpr
    rintro u ⟨neg, i, a, rfl⟩
    change naturalRestriction K r (rootElement K r neg i a) ∈
      CFSGSymplecticSerreMatrices.elementaryRootGroup K r
    rw [naturalRestriction_root]
    exact CFSGSymplecticSerreMatrices.rootTransvection_mem K r neg i _
  rw [rootElements_generate] at hle
  rintro y ⟨g, rfl⟩
  exact hle (Subgroup.mem_top g)

theorem restriction_range_eq [Finite K] (r : ℕ) :
    (naturalRestriction K r).range = CFSGSymplecticSerreMatrices.elementaryRootGroup K r := by
  apply le_antisymm (restriction_range_le K r)
  apply (Subgroup.closure_le _).mpr
  rintro u ⟨neg, i, a, rfl⟩
  by_cases hi : i.val + 1 < r
  · refine ⟨rootElement K r neg i a, ?_⟩
    rw [naturalRestriction_root, if_pos hi]
  · obtain ⟨t, ht⟩ := isSquare_of_charTwo' a
    have ht' : t ^ 2 = a := by simpa only [pow_two] using ht.symm
    refine ⟨rootElement K r neg i t, ?_⟩
    rw [naturalRestriction_root, if_neg hi, ht']

def restrictionIntoC (r : ℕ) : elementaryRootGroup K r →*
    CFSGSymplecticSerreMatrices.elementaryRootGroup K r :=
  (naturalRestriction K r).codRestrict (CFSGSymplecticSerreMatrices.elementaryRootGroup K r)
    (fun g => restriction_range_le K r ⟨g, rfl⟩)

theorem restrictionIntoC_surjective [Finite K] (r : ℕ) :
    Function.Surjective (restrictionIntoC K r) := by
  intro y
  have hy : y.val ∈ (naturalRestriction K r).range := by
    rw [restriction_range_eq]
    exact y.property
  obtain ⟨g, hg⟩ := hy
  exact ⟨g, Subtype.ext hg⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCharTwoRange
