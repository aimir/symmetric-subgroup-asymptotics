import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneRootLineLabel

/-! A nonidentity actual long root belongs to the original root subgroup
labelled by its SAME natural displacement range. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent
variable {K : Type} [Field K] [Finite K]

theorem mem_conjugateRootLine_iff_exists (h2 : (2 : K) ≠ 0) (s : ℕ)
    (g x : elementaryRootGroup K (s + 3)) :
    x ∈ conjugateRootLine h2 s g ↔ ∃ a : K, x = g * highestRoot s a * g⁻¹ := by
  constructor
  · rintro ⟨y, hy, he⟩
    obtain ⟨a, ha⟩ := (mem_highestRootLine_iff h2 s y).mp hy
    refine ⟨a, ?_⟩
    change g * y * g⁻¹ = x at he
    simpa only [ha] using he.symm
  · rintro ⟨a, rfl⟩
    exact ⟨highestRoot s a, (mem_highestRootLine_iff h2 s _).mpr ⟨a, rfl⟩, rfl⟩

theorem longRoot_mem_line_of_range (h2 : (2 : K) ≠ 0) (s : ℕ)
    (g : elementaryRootGroup K (s + 3)) (x : elementaryRootGroup K (s + 3))
    (hx : IsLongRootElement s x) (hn : x ≠ 1)
    (hr : LinearMap.range (Matrix.mulVecLin ((x.val : Mat K (s + 3)) - 1)) =
      conjugateRootPlane (K := K) s g) : x ∈ conjugateRootLine h2 s g := by
  obtain ⟨k, a, rfl⟩ := hx
  have ha : a ≠ 0 := by
    intro ha
    apply hn
    rw [ha, highestRoot_zero h2 s, mul_one, mul_inv_cancel]
  have hp : conjugateRootPlane (K := K) s k = conjugateRootPlane (K := K) s g :=
    (conjugate_highestRoot_displacement_range h2 s k a ha).symm.trans hr
  have hL := (conjugateRootLine_eq_iff_plane_eq h2 s k g).mpr hp
  rw [← hL]
  exact ⟨highestRoot s a, (mem_highestRootLine_iff h2 s _).mpr ⟨a, rfl⟩, rfl⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots
