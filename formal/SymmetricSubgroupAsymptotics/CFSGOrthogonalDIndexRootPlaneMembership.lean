import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootDisplacements

/-! A nonidentity actual D root belongs to the original root subgroup
labelled by its SAME natural displacement range. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootDisplacements
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPairOperator
open CFSGOrthogonalDIndexPlaneRootLine CFSGOrthogonalDIndexRootPlaneImage
variable {K : Type} [Field K]

theorem mem_conjugateRootLine_iff_exists (s : ℕ)
    (g x : elementaryRootGroup K (s + 4)) :
    x ∈ conjugateRootLine K s g ↔ ∃ a : K, x = g * highestRoot K s a * g⁻¹ := by
  constructor
  · rintro ⟨y, hy, he⟩
    obtain ⟨a, ha⟩ := (mem_highestRootLine_iff K s y).mp hy
    refine ⟨a, ?_⟩
    change g * y * g⁻¹ = x at he
    simpa only [ha] using he.symm
  · rintro ⟨a, rfl⟩
    exact ⟨highestRoot K s a, (mem_highestRootLine_iff K s _).mpr ⟨a, rfl⟩, rfl⟩

theorem root_mem_line_of_range (s : ℕ)
    (g : elementaryRootGroup K (s + 4)) (x : elementaryRootGroup K (s + 4))
    (hx : IsRootElement s x) (hn : x ≠ 1)
    (hr : LinearMap.range (Matrix.mulVecLin ((x.val : Mat K (s + 4)) - 1)) =
      conjugateRootPlane K s g) : x ∈ conjugateRootLine K s g := by
  obtain ⟨k, a, rfl⟩ := hx
  have ha : a ≠ 0 := by
    intro ha
    apply hn
    rw [ha, highestRoot_zero K s, mul_one, mul_inv_cancel]
  have hp : conjugateRootPlane K s k = conjugateRootPlane K s g :=
    (conjugate_highestRoot_displacement_range K s k a ha).symm.trans hr
  have hL := (conjugateRootLine_eq_iff_plane_eq K s k g).mpr hp
  rw [← hL]
  exact ⟨highestRoot K s a, (mem_highestRootLine_iff K s _).mpr ⟨a, rfl⟩, rfl⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootDisplacements
