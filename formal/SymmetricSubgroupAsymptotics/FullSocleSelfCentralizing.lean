import SymmetricSubgroupAsymptotics.ZmudFixedSpaceConstituents
import SymmetricSubgroupAsymptotics.SemisimpleOuterFibre

/-! A centerless FULL finite-group socle has trivial ambient centralizer.
No primitive action or classification hypothesis is needed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.FullSocleSelfCentralizing

theorem centralizer_eq_bot {G : Type} [Group G] [Finite G]
    (hS : IsCenterless (finiteGroupSocle G)) :
    Subgroup.centralizer (finiteGroupSocle G : Set G) = ⊥ := by
  let C := Subgroup.centralizer (finiteGroupSocle G : Set G)
  by_contra hC
  have hCn : C.Normal := inferInstance
  let good : Subgroup G → Prop := fun N => N.Normal ∧ N ≠ ⊥
  obtain ⟨N, hNC, hN⟩ := Finite.exists_le_minimal
    (p := good) (a := C) ⟨hCn, hC⟩
  have hmin : IsMinimalNormalSubgroup N := by
    refine ⟨hN.1.1, hN.1.2, ?_⟩
    intro M hMn hMne hMN
    exact hN.eq_of_le ⟨hMn, hMne⟩ hMN
  have hNS : N ≤ finiteGroupSocle G := by
    intro n hn
    exact Subgroup.subset_normalClosure ⟨N, hmin, hn⟩
  apply hN.1.2
  apply bot_unique
  intro n hn
  have hs : (⟨n, hNS hn⟩ : finiteGroupSocle G) = 1 := by
    apply hS
    intro t
    apply Subtype.ext
    have he : Commute (t : G) n :=
      Subgroup.mem_centralizer_iff.mp (hNC hn) t t.property
    exact he.symm.eq
  exact congrArg Subtype.val hs

theorem selfCentralizing {G : Type} [Group G] [Finite G]
    (hS : IsCenterless (finiteGroupSocle G)) (g : G)
    (hg : ∀ s : finiteGroupSocle G, g * s = s * g) :
    g ∈ finiteGroupSocle G := by
  have hm : g ∈ Subgroup.centralizer (finiteGroupSocle G : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro s hs
    exact (hg ⟨s, hs⟩).symm
  rw [centralizer_eq_bot hS] at hm
  exact (Subgroup.mem_bot.mp hm) ▸ (finiteGroupSocle G).one_mem

end SymmetricSubgroupAsymptotics.FullSocleSelfCentralizing
