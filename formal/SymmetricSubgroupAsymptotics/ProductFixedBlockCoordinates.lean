import SymmetricSubgroupAsymptotics.ProductBlockFrameWreathEmbedding

/-! An actual frame with trivial top has faithful direct-product local
coordinates. No independent local factors are assumed in its image. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame
variable {X I F : Type} {U : Subgroup (Equiv.Perm X)}
  (C : ProductBlockFrame U I F) (hC : ∀ u, C.top u=1)

def fixedCoordinates : U →* (I → Equiv.Perm F) where
  toFun u := (C.wreathEmbedding u).left
  map_one' := by
    change (C.wreathEmbedding 1).left=1
    rw [map_one]
    rfl
  map_mul' u v := by
    rw [map_mul]
    funext i
    change (C.wreathEmbedding u).left i*
      (C.wreathEmbedding v).left ((C.top u)⁻¹ i)=_
    rw [hC u]
    rfl

theorem fixedCoordinates_apply (u : U) (i : I) (x : F) :
    C.fixedCoordinates hC u i x=(C.frame.symm ((u : Equiv.Perm X) (C.frame (i,x)))).2 := by
  change (C.frame.symm ((u : Equiv.Perm X)
    (C.frame ((C.top u)⁻¹ i,x)))).2=_
  rw [hC u]
  rfl

theorem fixedCoordinates_injective : Function.Injective (C.fixedCoordinates hC) := by
  intro u v h
  apply C.wreathEmbedding_injective
  apply PermutationalWreathProduct.ext
  · exact h
  · change C.top u=C.top v
    rw [hC u,hC v]

end SymmetricSubgroupAsymptotics.ProductBlockFrame
