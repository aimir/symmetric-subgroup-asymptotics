import SymmetricSubgroupAsymptotics.AbelianNormalSocleCentralization
import SymmetricSubgroupAsymptotics.CyclicSocleQuotientTools

/-! Small structural socle lemmas for the four-block binary quotient
models. A three-cycle on the three nonidentity elements proves a literal
Klein line minimal; minimal lines spanning a self-centralizing abelian
kernel identify the whole socle without an assumed generator bound. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace FourPairBinarySocleLines

/-- A checked three-cycle on a literal four-element normal subgroup
makes that subgroup minimal normal in the actual ambient group. -/
theorem minimal_of_threeCycle {G : Type} [Group G]
    (V : Subgroup G) [V.Normal] (u v g : G)
    (hu : u ∈ V) (hv : v ∈ V) (hune : u ≠ 1)
    (hspan : Subgroup.closure ({u, v} : Set G) = V)
    (hcases : ∀ x ∈ V, x = 1 ∨ x = u ∨ x = v ∨ x = u*v)
    (hcycle1 : g*u*g⁻¹ = v) (hcycle2 : g*v*g⁻¹ = u*v)
    (hcycle3 : g*(u*v)*g⁻¹ = u) : IsMinimalNormalSubgroup V := by
  refine ⟨inferInstance, ?_, ?_⟩
  · intro hbot
    exact hune (Subgroup.mem_bot.mp (hbot ▸ hu))
  · intro W hW hWne hWV
    obtain ⟨x, hx, hxne⟩ := W.bot_or_exists_ne_one.resolve_left hWne
    have huW : u ∈ W := by
      rcases hcases x (hWV hx) with hx1 | hxu | hxv | hxuv
      · exact False.elim (hxne hx1)
      · exact hxu ▸ hx
      · have h1 : u*v ∈ W := by
          rw [← hcycle2]
          exact hW.conj_mem v (hxv ▸ hx) g
        rw [← hcycle3]
        exact hW.conj_mem (u*v) h1 g
      · rw [← hcycle3]
        exact hW.conj_mem (u*v) (hxuv ▸ hx) g
    have hvW : v ∈ W := by
      rw [← hcycle1]
      exact hW.conj_mem u huW g
    apply le_antisymm hWV
    rw [← hspan]
    apply (Subgroup.closure_le _).mpr
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact huW
    · exact (Set.mem_singleton_iff.mp hy) ▸ hvW

/-- The kernel of an actual binary quotient is the whole socle when
minimal normal lines span it and its centralizer is no larger. -/
theorem socle_eq_of_minimal_lines {G I : Type} [Group G]
    (V : Subgroup G) [V.Normal] [IsMulCommutative V]
    (lines : I → Subgroup G)
    (hminimal : ∀ i, IsMinimalNormalSubgroup (lines i))
    (hspan : (⨆ i, lines i) = V)
    (hcentral : Subgroup.centralizer (V : Set G) ≤ V) :
    finiteGroupSocle G = V := by
  apply le_antisymm
  · exact (finiteGroupSocle_le_centralizer_of_abelian_normal V).trans hcentral
  · rw [← hspan]
    apply iSup_le
    intro i x hx
    exact Subgroup.subset_normalClosure ⟨lines i, hminimal i, hx⟩

end FourPairBinarySocleLines
end SymmetricSubgroupAsymptotics
