import Mathlib.Algebra.Group.Subgroup.Basic

/-! Exact kernel control for a normalizer lift.  In the application the
kernel is the original translation subgroup and P is the actual Sylow 3.
The injectivity premise concerns only P, never the whole original group. -/
set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics.NormalizerKernelCentralizes

variable {G H : Type*} [Group G] [Group H]

theorem conjugate_eq (f : G →* H) (P : Subgroup G)
    (hinj : Function.Injective (f.comp P.subtype))
    (e : G) (he : e ∈ f.ker) (hn : e ∈ Subgroup.normalizer (P : Set G))
    (s : G) (hs : s ∈ P) : e * s * e⁻¹ = s := by
  have hmem : e * s * e⁻¹ ∈ P := (hn s).mp hs
  have hval : f e = 1 := MonoidHom.mem_ker.mp he
  have h := hinj (a₁ := ⟨e * s * e⁻¹, hmem⟩) (a₂ := ⟨s, hs⟩)
    (by simp [MonoidHom.comp_apply, hval])
  exact congrArg Subtype.val h

theorem normalizing_square_eq_one (f : G →* H) (P : Subgroup G)
    (hfixed : ∀ e : G, e ∈ f.ker →
      e ∈ Subgroup.normalizer (P : Set G) → e = 1)
    (g : G) (hg : g ∈ Subgroup.normalizer (P : Set G))
    (himage : (f g)^2 = 1) : g^2 = 1 := by
  apply hfixed
  · apply MonoidHom.mem_ker.mpr
    simpa only [map_pow] using himage
  · exact (Subgroup.normalizer (P : Set G)).pow_mem hg 2

end SymmetricSubgroupAsymptotics.NormalizerKernelCentralizes
