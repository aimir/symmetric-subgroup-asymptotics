import Mathlib.Algebra.Group.Subgroup.Basic

/-! A central cubic kernel and an actual exponent-two section force a
unique characteristic binary complement. This splits only the supplied
centralizer preimage, never an ambient affine extension. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CentralCubicRegularBinaryComplement

variable {D R : Type} [Group D] [Group R]
  (pi : D →* R) (l : R →* D)
  (hsection : ∀ r, pi (l r)=r)
  (hbinary : ∀ r : R, r^2=1)
  (hcubic : ∀ k : pi.ker, k^3=1)
  (hcentral : ∀ (k : pi.ker) (d : D), Commute (k : D) d)

include hsection hbinary hcubic hcentral in
/-- The complement is the intrinsic square-one set, including identity. -/
theorem mem_range_iff_square (x : D) : x∈l.range ↔ x^2=1 := by
  constructor
  · rintro ⟨r,rfl⟩
    rw [← map_pow,hbinary,map_one]
  · intro hx
    let t : D := (l (pi x))⁻¹*x
    have ht : t∈pi.ker := by
      change pi ((l (pi x))⁻¹*x)=1
      rw [map_mul,map_inv,hsection,inv_mul_cancel]
    have ht3 : t^3=1 := congrArg (fun z : pi.ker => (z : D)) (hcubic ⟨t,ht⟩)
    have hl2 : (l (pi x))^2=1 := by rw [← map_pow,hbinary,map_one]
    have hd : l (pi x)*t=x := by dsimp [t]; exact mul_inv_cancel_left _ _
    have hm : Commute (l (pi x)) t := (hcentral ⟨t,ht⟩ (l (pi x))).symm
    have ht2 : t^2=1 := by
      have hh : (l (pi x)*t)^2=1 := by rw [hd]; exact hx
      rwa [hm.mul_pow,hl2,one_mul] at hh
    have ht1 : t=1 := by
      rw [pow_succ,ht2,one_mul] at ht3
      exact ht3
    exact ⟨pi x,by simpa only [ht1,mul_one] using hd⟩

include hsection hbinary hcubic hcentral in
/-- Every automorphism of this actual centralizer preimage preserves the
chosen complement, so a separate Sylow-conjugacy choice is unnecessary. -/
theorem characteristic_range : l.range.Characteristic := by
  apply Subgroup.characteristic_iff_le_comap.mpr
  intro a x hx
  change a x∈l.range
  apply (mem_range_iff_square pi l hsection hbinary hcubic hcentral (a x)).mpr
  rw [← map_pow,(mem_range_iff_square pi l hsection hbinary hcubic hcentral x).mp hx,map_one]

include hsection hbinary hcubic hcentral in
/-- Any other homomorphic section is literally the same section. -/
theorem section_unique (s : R →* D) (hs : ∀ r, pi (s r)=r) : s=l := by
  apply MonoidHom.ext
  intro r
  have hh : (s r)^2=1 := by rw [← map_pow,hbinary,map_one]
  obtain ⟨u,hu⟩ := (mem_range_iff_square pi l hsection hbinary hcubic hcentral (s r)).mpr hh
  have hur : u=r := by
    have he := congrArg pi hu
    simpa only [hsection,hs] using he
  simpa only [hur] using hu.symm

end SymmetricSubgroupAsymptotics.CentralCubicRegularBinaryComplement
