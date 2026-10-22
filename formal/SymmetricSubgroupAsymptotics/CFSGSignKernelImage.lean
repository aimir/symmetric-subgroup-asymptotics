import Mathlib.GroupTheory.SpecificGroups.Alternating

/-! If the kernel of an action contains an odd element of H, the even
part of H has the SAME action image. The parity correction is retained
as an actual element of H, rather than an order or index estimate. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGSignKernelImage
variable {G D : Type*} [Group G] [Group D]

theorem map_eq_map_inf_ker (H : Subgroup G) (f : G →* D) (sgn : G →* ℤˣ)
    (t : G) (ht : t ∈ H) (hft : f t = 1) (hst : sgn t = -1) :
    H.map f = (H ⊓ sgn.ker).map f := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    rcases Int.units_eq_one_or (sgn g) with hs | hs
    · exact ⟨g, ⟨hg, hs⟩, rfl⟩
    · refine ⟨g * t, ⟨H.mul_mem hg ht, ?_⟩, ?_⟩
      · change sgn (g * t) = 1
        rw [map_mul, hs, hst]
        norm_num
      · rw [map_mul, hft, mul_one]
  · exact Subgroup.map_mono inf_le_left

end SymmetricSubgroupAsymptotics.CFSGSignKernelImage
