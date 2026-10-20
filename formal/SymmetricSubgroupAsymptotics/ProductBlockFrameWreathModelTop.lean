import SymmetricSubgroupAsymptotics.ProductBlockFrameWreathEmbedding

/-! Retain the original physical coordinates while replacing only the
faithful model of the block top. The original subgroup is unchanged. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame
variable {X I F R : Type} {U : Subgroup (Equiv.Perm X)} [Group R] [MulAction R I]
    (C : ProductBlockFrame U I F) (b : U →* R)
    (htop : ∀ u,C.top u=MulAction.toPermHom R I (b u))

def wreathEmbeddingOfTop : U →* PermutationalWreathProduct (Equiv.Perm F) R I where
  toFun u := ⟨(C.wreathEmbedding u).left,b u⟩
  map_one' := by
    apply PermutationalWreathProduct.ext
    · exact congrArg (fun z : PermutationalWreathProduct (Equiv.Perm F) (Equiv.Perm I) I => z.left) C.wreathEmbedding.map_one
    · exact b.map_one
  map_mul' u v := by
    apply PermutationalWreathProduct.ext
    · funext i
      have h := congrArg (fun z : PermutationalWreathProduct (Equiv.Perm F) (Equiv.Perm I) I => z.left i)
        (C.wreathEmbedding.map_mul u v)
      change (C.wreathEmbedding (u*v)).left i=
        (C.wreathEmbedding u).left i*(C.wreathEmbedding v).left ((C.top u)⁻¹ i) at h
      change (C.wreathEmbedding (u*v)).left i=
        (C.wreathEmbedding u).left i*(C.wreathEmbedding v).left ((b u)⁻¹ • i)
      simpa only [htop,← map_inv] using h
    · exact b.map_mul u v

@[simp] theorem wreathEmbeddingOfTop_right (u : U) :
    (wreathEmbeddingOfTop C b htop u).right=b u := rfl

 theorem wreathEmbeddingOfTop_injective : Function.Injective (wreathEmbeddingOfTop C b htop) := by
  intro u v h
  apply C.wreathEmbedding_injective
  apply PermutationalWreathProduct.ext
  · exact congrArg (fun z : PermutationalWreathProduct (Equiv.Perm F) R I => z.left) h
  · change C.top u=C.top v
    rw [htop,htop]
    exact congrArg (MulAction.toPermHom R I) (congrArg PermutationalWreathProduct.right h)
end SymmetricSubgroupAsymptotics.ProductBlockFrame
