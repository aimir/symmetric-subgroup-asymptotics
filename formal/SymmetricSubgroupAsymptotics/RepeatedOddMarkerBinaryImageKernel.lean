import SymmetricSubgroupAsymptotics.RepeatedOddMarkerImage

/-!
# Full ternary coordinates from the actual binary contraction image

Only the literal image of H must be binary; the ambient exterior need not
be binary. Powers of the same original element kill its entire image and
preserve a selected original 3-cycle. This gives the full-coordinate
kernel condition used in the exact admissible-state sum.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.RepeatedOddMarkerBinaryImageKernel

open RepeatedOddMarkerKernel RepeatedOddMarkerModule RepeatedOddMarkerImage

variable {ι D : Type*} [Group D]

private theorem alternating_pow_four_pow (g : OddMarkerGroup)
    (hg : g ∈ oddMarkerSign.ker) (k : ℕ) : g^(4^k)=g := by
  have hg4 : g^4=g := by
    rw [show (4:ℕ)=3+1 by rfl,pow_succ,oddMarker_kernel_cube g hg,one_mul]
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ,pow_mul,ih,hg4]

theorem jointKernel_coordinate_full (H : Subgroup ((ι → OddMarkerGroup) × D))
    (hB : IsPGroup 2 (image H)) (i : ι) (hfull : H.map (coordinate i)=⊤) :
    (jointKernel H).map (coordinate i)=oddMarkerSign.ker := by
  apply le_antisymm
  · rintro g ⟨x,hx,rfl⟩
    exact ((mem_jointKernel H x).mp hx).2.1 i
  · intro g hg
    have hm : g ∈ H.map (coordinate i) := by rw [hfull]; trivial
    obtain ⟨x,hx,hxi⟩ := Subgroup.mem_map.mp hm
    obtain ⟨k,hk⟩ := hB (quotientMap H ⟨x,hx⟩)
    have hk' : (quotientMap H ⟨x,hx⟩)^(4^k)=1 := by
      rw [show (4:ℕ)^k=2^k*2^k by simpa using (mul_pow (2:ℕ) 2 k),pow_mul,hk,one_pow]
    have hc : contraction (x^(4^k))=1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk'
    apply Subgroup.mem_map.mpr
    refine ⟨x^(4^k),⟨H.pow_mem hx _,hc⟩,?_⟩
    rw [map_pow,hxi]
    exact alternating_pow_four_pow g hg k

theorem coordinate_surjective (H : Subgroup ((ι → OddMarkerGroup) × D))
    (hB : IsPGroup 2 (image H)) (i : ι) (hfull : H.map (coordinate i)=⊤) :
    Function.Surjective (fun v : kernelSubmodule H => v.1 i) := by
  intro z
  have hm : (OddMarkerTernaryChart.chart (Multiplicative.ofAdd z) : OddMarkerGroup) ∈
      (jointKernel H).map (coordinate i) := by
    rw [jointKernel_coordinate_full H hB i hfull]
    exact (OddMarkerTernaryChart.chart (Multiplicative.ofAdd z)).property
  obtain ⟨x,hx,hxi⟩ := Subgroup.mem_map.mp hm
  obtain ⟨v,hv⟩ := (RepeatedOddMarkerModule.kernelEquiv H).surjective ⟨x,hx⟩
  refine ⟨v.toAdd,?_⟩
  have hc := congrArg (fun y : jointKernel H => y.1.1 i) hv
  have he : OddMarkerTernaryChart.chart (Multiplicative.ofAdd (v.toAdd.1 i)) =
      OddMarkerTernaryChart.chart (Multiplicative.ofAdd z) :=
    Subtype.ext (hc.trans hxi)
  exact congrArg Multiplicative.toAdd (OddMarkerTernaryChart.chart.injective he)

end SymmetricSubgroupAsymptotics.RepeatedOddMarkerBinaryImageKernel

end
