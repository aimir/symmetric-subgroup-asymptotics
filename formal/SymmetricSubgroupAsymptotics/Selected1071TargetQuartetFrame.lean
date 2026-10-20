import SymmetricSubgroupAsymptotics.Selected1071OriginalQuotientEquiv
import SymmetricSubgroupAsymptotics.ProductFixedBlockCoordinates

/-! Three literal fixed quartets in the selected twelve-point target.
Only original target-generator point images establish this frame. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1071QuotientGraph

private theorem target_preserves : ∀ (j : Fin 4),
    ProductBlockFrame.Preserves (finProdFinEquiv : Fin 3 × Fin 4 ≃ Fin 12)
      (targetGenerators j) (1 : Equiv.Perm (Fin 3)) := by
  change ∀ (j : Fin 4) (p : Fin 3 × Fin 4),
    ((finProdFinEquiv : Fin 3 × Fin 4 ≃ Fin 12).symm
      (targetGenerators j ((finProdFinEquiv : Fin 3 × Fin 4 ≃ Fin 12) p))).1=p.1
  decide +kernel

def targetQuartetFrame : ProductBlockFrame literalTarget (Fin 3) (Fin 4) :=
  ProductBlockFrame.ofGenerators (finProdFinEquiv : Fin 3 × Fin 4 ≃ Fin 12) targetGenerators (fun _ => 1) target_preserves

theorem targetQuartetFrame_top (g : literalTarget) : targetQuartetFrame.top g=1 := by
  have hr : targetQuartetFrame.top.range=⊥ := by
    change (ProductBlockFrame.ofGenerators (finProdFinEquiv : Fin 3 × Fin 4 ≃ Fin 12) targetGenerators
      (fun _ => 1) target_preserves).top.range=⊥
    rw [ProductBlockFrame.ofGenerators_top_range]
    simp
  have hg : targetQuartetFrame.top g∈targetQuartetFrame.top.range := ⟨g,rfl⟩
  rw [hr] at hg
  exact hg

def targetLocals : literalTarget →* (Fin 3 → Equiv.Perm (Fin 4)) :=
  targetQuartetFrame.fixedCoordinates targetQuartetFrame_top

theorem targetLocals_injective : Function.Injective targetLocals :=
  targetQuartetFrame.fixedCoordinates_injective targetQuartetFrame_top

theorem targetLocals_apply (g : literalTarget) (j : Fin 3) (x : Fin 4) :
    targetLocals g j x=
      ((finProdFinEquiv : Fin 3 × Fin 4 ≃ Fin 12).symm ((g : Equiv.Perm (Fin 12)) ((finProdFinEquiv : Fin 3 × Fin 4 ≃ Fin 12) (j,x)))).2 :=
  targetQuartetFrame.fixedCoordinates_apply targetQuartetFrame_top g j x

end SymmetricSubgroupAsymptotics.Selected1071QuotientGraph
