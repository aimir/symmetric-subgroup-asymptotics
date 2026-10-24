import SymmetricSubgroupAsymptotics.SchurPGroupCapacity

/-! A normal defining-characteristic p-subgroup is invisible in an actual
irreducible finite representation. Faithfulness therefore makes it
trivial. The fixed vector comes from the existing p-group theorem; the
normal subgroup's actual invariant subspace is preserved by the whole
group by Mathlib's normal-invariants lemma. No classification or
ordinary-generator assertion is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.IrreducibleLinearNormalPSubgroup

variable {p : ℕ} [Fact p.Prime] {H V : Type} [Group H]
    [AddCommGroup V] [Module (ZMod p) V] [Finite V] [Nontrivial V]
    (rho : Representation (ZMod p) H V)
    (hirr : ∀ W : Submodule (ZMod p) V,
      (∀ (h : H) (v : V), v ∈ W → rho h v ∈ W) → W = ⊥ ∨ W = ⊤)

include hirr

theorem normal_p_subgroup_le_kernel (N : Subgroup H) [N.Normal]
    (hN : IsPGroup p N) : N ≤ rho.ker := by
  let W : Submodule (ZMod p) V := Representation.invariants (rho.comp N.subtype)
  obtain ⟨v,hv,hfixed⟩ := pGroup_representation_nonzero_fixed hN (rho.comp N.subtype)
  have hvW : v ∈ W := hfixed
  have hstable : ∀ (h : H) (w : V), w ∈ W → rho h w ∈ W :=
    fun h _ hw => Representation.le_comap_invariants rho N h hw
  have htop : W = ⊤ := (hirr W hstable).resolve_left (by
    intro hbot
    apply hv
    have hm : v ∈ (⊥ : Submodule (ZMod p) V) := hbot ▸ hvW
    simpa only [Submodule.mem_bot] using hm)
  intro n hn
  change rho n = 1
  apply LinearMap.ext
  intro w
  have hw : w ∈ W := by rw [htop]; trivial
  change rho n w = w
  exact hw ⟨n,hn⟩

theorem normal_p_subgroup_eq_bot (hrho : Function.Injective rho)
    (N : Subgroup H) [N.Normal] (hN : IsPGroup p N) : N = ⊥ := by
  have hle := normal_p_subgroup_le_kernel rho hirr N hN
  have hker : rho.ker = ⊥ := (MonoidHom.ker_eq_bot_iff rho).mpr hrho
  exact le_antisymm (hle.trans_eq hker) bot_le

end SymmetricSubgroupAsymptotics.IrreducibleLinearNormalPSubgroup
