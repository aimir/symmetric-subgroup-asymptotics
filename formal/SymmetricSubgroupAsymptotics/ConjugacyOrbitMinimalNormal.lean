import SymmetricSubgroupAsymptotics.ZmudFaithfulCharacterInput

/-! A single ambient conjugacy orbit on the nonidentity elements supplies
actual minimal normality, without enumerating normal subgroups. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics

 theorem minimalNormal_of_nonidentity_conjugacy_orbit
    {G : Type} [Group G] (D : Subgroup G) [D.Normal] (hD : D≠⊥)
    (horbit : ∀ x∈D, x≠1 → ∀ y∈D, y≠1 → ∃ g : G, g*x*g⁻¹=y) :
    IsMinimalNormalSubgroup D := by
  refine ⟨inferInstance,hD,?_⟩
  intro H hH hHne hHD
  obtain hbot | ⟨x,hx,hxne⟩ := H.bot_or_exists_ne_one
  · exact False.elim (hHne hbot)
  apply le_antisymm hHD
  intro y hy
  by_cases hyone : y=1
  · exact hyone.symm ▸ H.one_mem
  obtain ⟨g,hg⟩ := horbit x (hHD hx) hxne y hy hyone
  exact hg ▸ hH.conj_mem x hx g

end SymmetricSubgroupAsymptotics
