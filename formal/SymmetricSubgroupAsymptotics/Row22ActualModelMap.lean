import SymmetricSubgroupAsymptotics.Row22DirectedEdgeModel
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row22DirectedEdgeModel
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

private def first : Equiv.Perm (Fin 4) →* Model where
  toFun p := (p,1)
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem action_mem (g : Model) : action g ∈ Row22Top := by
  let P : Subgroup (Equiv.Perm (Fin 4)) := Row22Top.comap (action.comp first)
  have hcycle : finRotate 4 ∈ P := by
    change action (codes 1) ∈ Row22Top
    rw [generator_eq]
    exact Subgroup.subset_closure (Set.mem_range_self 1)
  have hswap : Equiv.swap (0 : Fin 4) 1 ∈ P := by
    change action (codes 0) ∈ Row22Top
    rw [generator_eq]
    exact Subgroup.subset_closure (Set.mem_range_self 0)
  have hcl : Subgroup.closure ({finRotate 4,Equiv.swap (0 : Fin 4) 1} :
      Set (Equiv.Perm (Fin 4))) = ⊤ := by
    exact Equiv.Perm.closure_cycle_adjacent_swap isCycle_finRotate
      support_finRotate (0 : Fin 4)
  have hle : Subgroup.closure ({finRotate 4,Equiv.swap (0 : Fin 4) 1} :
      Set (Equiv.Perm (Fin 4))) ≤ P := by
    apply (Subgroup.closure_le _).mpr
    intro p hp
    rcases Set.mem_insert_iff.mp hp with rfl | hp
    · exact hcycle
    · have he : p=Equiv.swap (0 : Fin 4) 1 := Set.mem_singleton_iff.mp hp
      exact he ▸ hswap
  rw [hcl] at hle
  have hp : action (g.1,1) ∈ Row22Top := hle (Subgroup.mem_top g.1)
  have hz : action (1,g.2) ∈ Row22Top := by
    have hcases : ∀ z : Bit, z=1 ∨ z=Multiplicative.ofAdd 1 := by decide +kernel
    rcases hcases g.2 with hz | hz
    · rw [hz]
      change action (1 : Model) ∈ Row22Top
      rw [map_one]
      exact Row22Top.one_mem
    · rw [hz]
      change action (codes 2) ∈ Row22Top
      rw [generator_eq]
      exact Subgroup.subset_closure (Set.mem_range_self 2)
  have he : g=(g.1,1)*(1,g.2) := by ext <;> simp
  rw [he,map_mul]
  exact Row22Top.mul_mem hp hz

def originalMap : Model →* Row22Top := action.codRestrict Row22Top action_mem

theorem originalMap_surjective : Function.Surjective originalMap := by
  have hle : Row22Top ≤ action.range := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨codes i,generator_eq i⟩
  intro u
  obtain ⟨g,hg⟩ := hle u.property
  exact ⟨g,Subtype.ext hg⟩

def originalEquiv : Model ≃* Row22Top :=
  MulEquiv.ofBijective originalMap ⟨fun _ _ h =>
    action_injective (congrArg Subtype.val h),originalMap_surjective⟩
end SymmetricSubgroupAsymptotics.Row22DirectedEdgeModel
