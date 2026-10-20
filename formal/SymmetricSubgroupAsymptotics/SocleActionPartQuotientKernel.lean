import SymmetricSubgroupAsymptotics.AbelianNormalSocleCentralization

/-! Actual quotient projection of socle action rows. These statements use
an epimorphism of the original groups, with its literal kernel. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace SocleActionPartQuotientKernel

variable {G H : Type} [Group G] [Group H]

/-- A nonzero image of a minimal normal subgroup is minimal normal. -/
theorem minimal_map (f : G →* H) (hf : Function.Surjective f)
    (M : Subgroup G) (hM : IsMinimalNormalSubgroup M)
    (hne : M.map f ≠ ⊥) : IsMinimalNormalSubgroup (M.map f) := by
  letI : M.Normal := hM.1
  refine ⟨Subgroup.Normal.map inferInstance f hf, hne, ?_⟩
  intro L hL hLne hLM
  let A : Subgroup G := M ⊓ L.comap f
  letI : L.Normal := hL
  have hAne : A ≠ ⊥ := by
    intro hAbot
    apply hLne
    apply le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hLM hx
    have hyA : y ∈ A := ⟨hy, by
      change f y∈L
      rw [hyx]
      exact hx⟩
    have hyone : y = 1 := Subgroup.mem_bot.mp (hAbot ▸ hyA)
    exact Subgroup.mem_bot.mpr (by simpa [hyone] using hyx.symm)
  have hAM : A = M := hM.2.2 A inferInstance hAne inf_le_left
  apply le_antisymm hLM
  rintro x ⟨y, hy, rfl⟩
  have hyA : y ∈ A := hAM.symm ▸ hy
  exact hyA.2

/-- Epimorphisms carry the actual socle into the actual quotient socle. -/
theorem socle_map_le (f : G →* H) (hf : Function.Surjective f) :
    (finiteGroupSocle G).map f ≤ finiteGroupSocle H := by
  apply Subgroup.map_le_iff_le_comap.mpr
  unfold finiteGroupSocle
  apply Subgroup.normalClosure_le_normal
  rintro x ⟨M, hM, hx⟩
  by_cases hbot : M.map f = ⊥
  · have hfx : f x ∈ (⊥ : Subgroup H) := hbot ▸ (show f x ∈ M.map f from ⟨x,hx,rfl⟩)
    have hxone : f x = 1 := Subgroup.mem_bot.mp hfx
    change f x ∈ Subgroup.normalClosure
      {g : H | ∃ L : Subgroup H, IsMinimalNormalSubgroup L ∧ g ∈ L}
    rw [hxone]
    exact Subgroup.one_mem _
  · exact Subgroup.subset_normalClosure
      ⟨M.map f, minimal_map f hf M hM hbot, ⟨x,hx,rfl⟩⟩

/-- If the separator becomes abelian in the linear quotient, every active
socle row lies in the actual projection kernel. -/
theorem active_le_kernel [Finite G]
    (f : G →* H) (hf : Function.Surjective f)
    (D : Subgroup G) [D.Normal] [IsMulCommutative (D.map f)] :
    nontrivialActionSoclePart G D ≤ f.ker := by
  letI : (D.map f).Normal := Subgroup.Normal.map inferInstance f hf
  apply minimalNormalSoclePart_le_of
  intro M hM hfull
  letI : M.Normal := hM.1
  have hMImage : M.map f ≤ finiteGroupSocle H :=
    (Subgroup.map_mono (show M ≤ finiteGroupSocle G from
      fun x hx ↦ Subgroup.subset_normalClosure ⟨M,hM,hx⟩)).trans
        (socle_map_le f hf)
  have hcentral : M.map f ≤ Subgroup.centralizer ((D.map f) : Set H) :=
    hMImage.trans (finiteGroupSocle_le_centralizer_of_abelian_normal (D.map f))
  have hzero : ⁅D.map f, M.map f⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentral
  have hmap : M.map f = ⊥ := by
    rw [← hfull, Subgroup.map_commutator, hzero]
  exact (Subgroup.map_eq_bot_iff (H := M)).mp hmap

end SocleActionPartQuotientKernel
end SymmetricSubgroupAsymptotics
