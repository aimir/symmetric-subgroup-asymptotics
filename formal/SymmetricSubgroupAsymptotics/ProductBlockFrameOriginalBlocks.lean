import SymmetricSubgroupAsymptotics.ProductBlockFrameGenerators
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockOfPrimitiveFibre

/-! The physical product chart supplies an actual equivariant block map and
an exact coordinate equivalence on each original fibre. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace ProductBlockFrame

variable {X I F : Type} {U : Subgroup (Equiv.Perm X)}
    (C : ProductBlockFrame U I F)

abbrev topMulAction : MulAction U I := MulAction.compHom I C.top

def blockMap (x : X) : I := (C.frame.symm x).1

theorem blockMap_equivariant (u : U) (x : X) :
    C.blockMap (u • x) = C.top u (C.blockMap x) := by
  simpa only [blockMap, C.frame.apply_symm_apply] using
    C.intertwine u (C.frame.symm x)

/-- This is the actual fibre on the original points, not a proxy action. -/
def originalFibreEquiv (i : I) : originalBlockFibre C.blockMap i ≃ F where
  toFun x := (C.frame.symm x.1).2
  invFun f := ⟨C.frame (i,f), by simp [blockMap]⟩
  left_inv x := by
    apply Subtype.ext
    have hx : (C.frame.symm x.1).1 = i := x.2
    have hp : C.frame.symm x.1 = (i,(C.frame.symm x.1).2) := Prod.ext hx rfl
    exact (congrArg C.frame hp).symm.trans (C.frame.apply_symm_apply x.1)
  right_inv f := by simp

theorem originalFibre_card (i : I) :
    Nat.card (originalBlockFibre C.blockMap i) = Nat.card F :=
  Nat.card_congr (C.originalFibreEquiv i)

variable [MulAction.IsPretransitive U X]

/-- Retain the chosen physical system when its actual component is primitive. -/
def minimalBlock :
    letI : MulAction U I := C.topMulAction
    (x₀ : X) → [Nontrivial (originalBlockFibre C.blockMap (C.blockMap x₀))] →
    (MulAction.IsPreprimitive
      (originalBlockComponent C.blockMap C.blockMap_equivariant (C.blockMap x₀))
      (originalBlockFibre C.blockMap (C.blockMap x₀))) →
    (MulAction.stabilizer U (C.blockMap x₀) < ⊤) →
    OriginalMinimalBlock (A := U) x₀ := by
  letI : MulAction U I := C.topMulAction
  intro x₀ _ hc hproper
  exact OriginalMinimalBlock.ofPrimitiveFibre C.blockMap C.blockMap_equivariant x₀ hc hproper

end ProductBlockFrame
end SymmetricSubgroupAsymptotics
end
