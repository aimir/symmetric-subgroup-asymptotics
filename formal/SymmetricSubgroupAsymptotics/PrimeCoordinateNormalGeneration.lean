import SymmetricSubgroupAsymptotics.PrimeTwoKernelOrbitNormalGeneration

/-! Actual prime-cyclic coordinates normally generate the original normal
subgroup in one position. The two-coordinate version includes coincident
coordinate kernels as well as a genuine two-kernel orbit; no nontriviality
or independent full-product assertion is presumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimeCoordinateNormalGeneration

theorem normalGen_le_one_of_injective_coordinate
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (p : ℕ) [Fact p.Prime]
    (f : N →* Multiplicative (ZMod p)) (hf : Function.Injective f) :
    MarkedC4.normalGen N ≤ 1 := by
  by_cases hbot : N = ⊥
  · rw [hbot,MarkedC4.normalGen_bot]
    omega
  letI : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hbot
  obtain ⟨x,hx⟩ := exists_ne (1 : N)
  have hfx : f x ≠ 1 := fun he => hx (hf (he.trans (map_one f).symm))
  let M : Subgroup G := Subgroup.normalClosure ({(x : G)} : Set G)
  have hxM : (x : G) ∈ M := Subgroup.subset_normalClosure (Set.mem_singleton _)
  have hcard : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p),Nat.card_zmod]
  have hcl : M = N := by
    apply le_antisymm
    · apply Subgroup.normalClosure_le_normal
      intro u hu
      have he : u = (x : G) := Set.mem_singleton_iff.mp hu
      rw [he]
      exact x.property
    · intro z hz
      let zN : N := ⟨z,hz⟩
      obtain ⟨a,ha⟩ := (Submonoid.mem_powers_iff (f zN) (f x)).mp
        (mem_powers_of_prime_card hcard hfx)
      have he : x^a = zN := hf (by simpa only [map_pow] using ha)
      have heG : (x : G)^a = z := congrArg Subtype.val he
      exact heG ▸ M.pow_mem hxM a
  have hh := MarkedC4.normalGen_le (N := N) (s := {(x : G)})
    (by simpa only [Finset.coe_singleton,Set.singleton_subset_iff] using x.property)
    (by simpa only [Finset.coe_singleton,M] using hcl)
  simpa only [Finset.card_singleton] using hh

theorem normalGen_le_one_of_two_coordinate_kernel_orbit
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (p : ℕ) [Fact p.Prime]
    (f g : N →* Multiplicative (ZMod p))
    (hjoint : Function.Injective (fun u : N => (f u,g u))) (h : G)
    (hfg : f.ker.map (MulAut.conjNormal h).toMonoidHom = g.ker)
    (hgf : g.ker.map (MulAut.conjNormal h).toMonoidHom = f.ker) :
    MarkedC4.normalGen N ≤ 1 := by
  by_cases heq : f.ker = g.ker
  · have hf : Function.Injective f := by
      intro u v he
      have hguv : g (u*v⁻¹) = 1 := by
        change u*v⁻¹ ∈ g.ker
        rw [←heq]
        change f (u*v⁻¹) = 1
        rw [map_mul,map_inv,he,mul_inv_cancel]
      have hge : g u = g v := mul_inv_eq_one.mp (by
        simpa only [map_mul,map_inv] using hguv)
      exact hjoint (Prod.ext he hge)
    exact normalGen_le_one_of_injective_coordinate N p f hf
  · exact PrimeTwoKernelOrbitNormalGeneration.normalGen_le_one_of_two_kernel_orbit
      N p f g hjoint h heq hfg hgf

end SymmetricSubgroupAsymptotics.PrimeCoordinateNormalGeneration
