import SymmetricSubgroupAsymptotics.ProductBlockFrameWreathEmbedding
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame
variable {X I F : Type} {U : Subgroup (Equiv.Perm X)} (C : ProductBlockFrame U I F)

 theorem wreathEmbedding_left_apply (u : U) (i : I) (x : F) :
    (C.wreathEmbedding u).left i x=
      (C.frame.symm ((u : Equiv.Perm X) (C.frame ((C.top u)⁻¹ i,x)))).2 := rfl
end SymmetricSubgroupAsymptotics.ProductBlockFrame
