import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.Basic

/-! Two actual prime-cyclic coordinates detect the original normal
subgroup. One actual axis element and its actual ambient conjugate then
normally generate it. There is no supplied module action, abstract normal
rank bound, independent coordinate subgroup, or ordinary-extension claim. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimeTwoAxisConjugateNormalGeneration

theorem normalGen_le_one_of_actual_conjugate_axes
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (p : ℕ) [Fact p.Prime]
    (f g : N →* Multiplicative (ZMod p))
    (hjoint : Function.Injective (fun u : N => (f u,g u)))
    (x : N) (hfx : f x ≠ 1) (hgx : g x = 1) (h : G)
    (hfy : f ((MulAut.conjNormal h) x) = 1)
    (hgy : g ((MulAut.conjNormal h) x) ≠ 1) :
    MarkedC4.normalGen N ≤ 1 := by
  let y : N := (MulAut.conjNormal h) x
  have hyf : f y = 1 := hfy
  have hyg : g y ≠ 1 := hgy
  let M : Subgroup G := Subgroup.normalClosure ({(x : G)} : Set G)
  have hxM : (x : G) ∈ M := Subgroup.subset_normalClosure (Set.mem_singleton _)
  have hyM : (y : G) ∈ M := by
    change h*(x : G)*h⁻¹ ∈ M
    exact (inferInstance : M.Normal).conj_mem (x : G) hxM h
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
      obtain ⟨b,hb⟩ := (Submonoid.mem_powers_iff (g zN) (g y)).mp
        (mem_powers_of_prime_card hcard hyg)
      have hxy : x^a*y^b = zN := by
        apply hjoint
        apply Prod.ext
        · change f (x^a*y^b) = f zN
          simpa only [map_mul,map_pow,hyf,one_pow,mul_one] using ha
        · change g (x^a*y^b) = g zN
          simpa only [map_mul,map_pow,hgx,one_pow,one_mul] using hb
      have hzM : (x : G)^a*(y : G)^b ∈ M :=
        M.mul_mem (M.pow_mem hxM a) (M.pow_mem hyM b)
      have he : (x : G)^a*(y : G)^b = z := congrArg Subtype.val hxy
      exact he ▸ hzM
  have hh := MarkedC4.normalGen_le (N := N) (s := {(x : G)})
    (by simpa only [Finset.coe_singleton,Set.singleton_subset_iff] using x.property)
    (by simpa only [Finset.coe_singleton,M] using hcl)
  simpa only [Finset.card_singleton] using hh

end SymmetricSubgroupAsymptotics.PrimeTwoAxisConjugateNormalGeneration
