import SymmetricSubgroupAsymptotics.Selected1542QuotientStructureData
import SymmetricSubgroupAsymptotics.ProductFixedBlockCoordinates

/-! Two literal fixed quartets in the selected eight-point target.
Only original target-generator point images establish this frame. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure

def literalTarget : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range targetGenerators)

private theorem target_preserves : ∀ (j : Fin 3),
    ProductBlockFrame.Preserves (finProdFinEquiv : Fin 2 × Fin 4 ≃ Fin 8)
      (targetGenerators j) (1 : Equiv.Perm (Fin 2)) := by
  change ∀ (j : Fin 3) (p : Fin 2 × Fin 4),
    ((finProdFinEquiv : Fin 2 × Fin 4 ≃ Fin 8).symm
      (targetGenerators j ((finProdFinEquiv : Fin 2 × Fin 4 ≃ Fin 8) p))).1=p.1
  decide +kernel

def targetQuartetFrame : ProductBlockFrame literalTarget (Fin 2) (Fin 4) :=
  ProductBlockFrame.ofGenerators (finProdFinEquiv : Fin 2 × Fin 4 ≃ Fin 8) targetGenerators (fun _ => 1) target_preserves

theorem targetQuartetFrame_top (g : literalTarget) : targetQuartetFrame.top g=1 := by
  have hr : targetQuartetFrame.top.range=⊥ := by
    change (ProductBlockFrame.ofGenerators (finProdFinEquiv : Fin 2 × Fin 4 ≃ Fin 8) targetGenerators
      (fun _ => 1) target_preserves).top.range=⊥
    rw [ProductBlockFrame.ofGenerators_top_range]
    simp
  have hg : targetQuartetFrame.top g∈targetQuartetFrame.top.range := ⟨g,rfl⟩
  rw [hr] at hg
  exact hg

def targetLocals : literalTarget →* (Fin 2 → Equiv.Perm (Fin 4)) :=
  targetQuartetFrame.fixedCoordinates targetQuartetFrame_top

theorem targetLocals_injective : Function.Injective targetLocals :=
  targetQuartetFrame.fixedCoordinates_injective targetQuartetFrame_top

theorem targetLocals_apply (g : literalTarget) (j : Fin 2) (x : Fin 4) :
    targetLocals g j x=
      ((finProdFinEquiv : Fin 2 × Fin 4 ≃ Fin 8).symm ((g : Equiv.Perm (Fin 8)) ((finProdFinEquiv : Fin 2 × Fin 4 ≃ Fin 8) (j,x)))).2 :=
  targetQuartetFrame.fixedCoordinates_apply targetQuartetFrame_top g j x

end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
