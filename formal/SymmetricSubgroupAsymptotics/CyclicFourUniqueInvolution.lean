import SymmetricSubgroupAsymptotics.CyclicFourInvolutionIntersection

/-! Any subgroup embedded in a cyclic group of order four has at most
one involution. In particular this applies to its order-two subgroup;
no equality with the whole ambient cyclic group is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CyclicFourUniqueInvolution
variable {G H : Type*} [Group G] [Finite G] [Group H]

theorem involution_eq_square (y x : G) (hy : orderOf y=4)
    (hx : x∈Subgroup.zpowers y) (hx2 : x^2=1) (hxne : x≠1) : x=y^2 := by
  classical
  obtain ⟨k,hk,he⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hx)
  have hk4 : k<4 := by simpa only [hy] using Finset.mem_range.mp hk
  have hy4 : y^4=1 := by rw [←hy]; exact pow_orderOf_eq_one y
  have hy2 : y^2≠1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [hy] at hd
    norm_num at hd
  have hk0 : k≠0 := by
    intro h
    exact hxne (he.symm.trans (by rw [h,pow_zero]))
  have hk1 : k≠1 := by
    intro h
    have hxy : x=y := he.symm.trans (by rw [h,pow_one])
    exact hy2 (hxy ▸ hx2)
  have hk3 : k≠3 := by
    intro h
    have h3 : (y^3)^2=1 := by simpa only [h] using (congrArg (fun z : G => z^2) he).trans hx2
    have h6 : y^(4+2)=1 := (pow_mul y 3 2).trans h3
    rw [pow_add,hy4,one_mul] at h6
    exact hy2 h6
  have hk2 : k=2 := by omega
  simpa only [hk2] using he.symm

theorem fixes_involution_of_embedding (i : H →* G) (hi : Function.Injective i)
    (y : G) (hy : orderOf y=4) (hcyclic : ∀ h : H,i h∈Subgroup.zpowers y)
    (f : MulAut H) (z : H) (hz2 : z^2=1) (hzne : z≠1) : f z=z := by
  have hzn : i z≠1 := fun h => hzne (hi (h.trans (map_one i).symm))
  have hfn : i (f z)≠1 := by
    intro h
    have hf : f z=1 := hi (h.trans (map_one i).symm)
    exact hzne (f.injective (hf.trans (map_one f).symm))
  have hz : i z=y^2 := involution_eq_square y (i z) hy (hcyclic z)
    ((map_pow i z 2).symm.trans ((congrArg i hz2).trans (map_one i))) hzn
  have hf : i (f z)=y^2 := involution_eq_square y (i (f z)) hy (hcyclic (f z))
    ((map_pow i (f z) 2).symm.trans
      ((congrArg i ((map_pow f z 2).symm.trans
        ((congrArg f hz2).trans (map_one f)))).trans (map_one i))) hfn
  exact hi (hf.trans hz.symm)

end SymmetricSubgroupAsymptotics.CyclicFourUniqueInvolution
