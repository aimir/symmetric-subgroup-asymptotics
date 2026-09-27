import SymmetricSubgroupAsymptotics.RepeatedOddMarkerImage

/-!
# Full original marker coordinates are constant on an exact state fibre

The actual image and literal ternary kernel determine whether all marker
coordinates are full S3, once the exterior is binary. In particular the
unrestricted fixed-image/fixed-kernel fibre of one full-coordinate state
does not accidentally include smaller coordinate images. No product-kernel
or independence assumption is made.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.RepeatedOddMarkerFullCoordinates

open RepeatedOddMarkerKernel RepeatedOddMarkerModule

private theorem full_of_kernel_and_odd (W : Subgroup OddMarkerGroup)
    (hker : oddMarkerSign.ker ≤ W) (hodd : ∃ h ∈ W, oddMarkerSign h ≠ 1) : W = ⊤ := by
  obtain ⟨h,hh,ho⟩ := hodd
  apply top_unique
  intro g _
  by_cases hg : oddMarkerSign g = 1
  · exact hker hg
  · have same : oddMarkerSign g = oddMarkerSign h := by
      have hc : ∀ s t : Multiplicative (ZMod 2), s≠1 → t≠1 → s=t := by decide +kernel
      exact hc _ _ hg ho
    have hk : g*h⁻¹ ∈ oddMarkerSign.ker := by
      change oddMarkerSign (g*h⁻¹)=1
      rw [map_mul,map_inv,same,mul_inv_cancel]
    simpa only [inv_mul_cancel_right] using W.mul_mem (hker hk) hh

variable {ι D : Type*} [Group D]

/-- A full ternary kernel coordinate and an actual odd coordinate
element together force the original S3 projection to be full. -/
theorem coordinate_full (H : Subgroup ((ι → OddMarkerGroup) × D)) (i : ι)
    (hkernel : Function.Surjective (fun v : kernelSubmodule H => v.1 i))
    (hodd : ∃ h ∈ H, oddMarkerSign (h.1 i) ≠ 1) :
    H.map (coordinate i)=⊤ := by
  apply full_of_kernel_and_odd
  · intro g hg
    let a := OddMarkerTernaryChart.chart.symm ⟨g,hg⟩
    obtain ⟨v,hv⟩ := hkernel a.toAdd
    change v.1 i = a.toAdd at hv
    apply Subgroup.mem_map.mpr
    refine ⟨reconstruction (Multiplicative.ofAdd v.1),v.2,?_⟩
    change (OddMarkerTernaryChart.chart (Multiplicative.ofAdd (v.1 i)) : OddMarkerGroup)=g
    rw [hv]
    exact congrArg Subtype.val (OddMarkerTernaryChart.chart.apply_symm_apply ⟨g,hg⟩)
  · obtain ⟨h,hh,ho⟩ := hodd
    exact ⟨h.1 i,Subgroup.mem_map.mpr ⟨h,hh,rfl⟩,ho⟩

theorem exists_odd (H : Subgroup ((ι → OddMarkerGroup) × D)) (i : ι)
    (hfull : H.map (coordinate i)=⊤) :
    ∃ h ∈ H, oddMarkerSign (h.1 i) ≠ 1 := by
  obtain ⟨b,hb⟩ := RepeatedOddMarkerImage.signCharacter_nontrivial H i hfull
  obtain ⟨h,rfl⟩ := RepeatedOddMarkerImage.quotientMap_surjective H b
  exact ⟨h.1,h.2,hb⟩

theorem coordinate_full_iff (hD : IsPGroup 2 D)
    (H : Subgroup ((ι → OddMarkerGroup) × D)) (i : ι) :
    H.map (coordinate i)=⊤ ↔
      Function.Surjective (fun v : kernelSubmodule H => v.1 i) ∧
      ∃ h ∈ H, oddMarkerSign (h.1 i)≠1 := by
  constructor
  · intro h
    exact ⟨coordinate_surjective hD H i h,exists_odd H i h⟩
  · rintro ⟨hk,ho⟩
    exact coordinate_full H i hk ho

/-- All original subgroups in this exact state fibre have the same full
coordinate property. The exterior and coordinate labels are unchanged. -/
theorem full_of_same_state (hD : IsPGroup 2 D)
    (H H' : Subgroup ((ι → OddMarkerGroup) × D))
    (himage : H.map contraction = H'.map contraction)
    (hkernel : kernelSubmodule H = kernelSubmodule H')
    (hfull : ∀ i, H.map (coordinate i)=⊤) :
    ∀ i, H'.map (coordinate i)=⊤ := by
  intro i
  apply coordinate_full
  · rw [← hkernel]
    exact coordinate_surjective hD H i (hfull i)
  · obtain ⟨h,hh,ho⟩ := exists_odd H i (hfull i)
    have hm : contraction h ∈ H'.map contraction := by
      rw [← himage]
      exact Subgroup.mem_map.mpr ⟨h,hh,rfl⟩
    obtain ⟨h',hh',he⟩ := Subgroup.mem_map.mp hm
    refine ⟨h',hh',?_⟩
    have hs := congrArg (fun b : (ι → Multiplicative (ZMod 2)) × D => b.1 i) he
    change oddMarkerSign (h'.1 i)=oddMarkerSign (h.1 i) at hs
    rw [hs]
    exact ho

end SymmetricSubgroupAsymptotics.RepeatedOddMarkerFullCoordinates

end
