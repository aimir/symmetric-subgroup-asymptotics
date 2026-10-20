import SymmetricSubgroupAsymptotics.ProductBlockFrameWreathEmbedding
import SymmetricSubgroupAsymptotics.PermutationalWreathTransport

/-! Corestrict a physical frame's wreath embedding to its actual top range
before transporting to a canonical block model. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame
variable {X I F : Type} {U : Subgroup (Equiv.Perm X)}
  (C : ProductBlockFrame U I F)

def actualTopWreath : U →*
    PermutationalWreathProduct (Equiv.Perm F) C.top.range I where
  toFun u := ⟨(C.wreathEmbedding u).left,C.top.rangeRestrict u⟩
  map_one' := by
    apply PermutationalWreathProduct.ext
    · exact congrArg (fun w : PermutationalWreathProduct (Equiv.Perm F) (Equiv.Perm I) I => w.left) C.wreathEmbedding.map_one
    · exact C.top.rangeRestrict.map_one
  map_mul' u v := by
    apply PermutationalWreathProduct.ext
    · exact congrArg (fun w : PermutationalWreathProduct (Equiv.Perm F) (Equiv.Perm I) I => w.left) (C.wreathEmbedding.map_mul u v)
    · exact C.top.rangeRestrict.map_mul u v

theorem actualTopWreath_injective : Function.Injective C.actualTopWreath := by
  intro u v h
  apply C.wreathEmbedding_injective
  apply PermutationalWreathProduct.ext
  · exact congrArg (fun w : PermutationalWreathProduct (Equiv.Perm F) C.top.range I => w.left) h
  · exact congrArg (fun w : PermutationalWreathProduct (Equiv.Perm F) C.top.range I =>
      (w.right : Equiv.Perm I)) h

variable {R J : Type} [Group R] [MulAction R J]
  (e : C.top.range ≃* R) (c : I ≃ J)
  (hc : ∀ b : C.top.range, ∀ i : I, c (b • i)=e b • c i)

/-- The canonical model still receives precisely the original subgroup. -/
def canonicalWreath : U →* PermutationalWreathProduct (Equiv.Perm F) R J :=
  (PermutationalWreathProduct.transport e c hc).toMonoidHom.comp C.actualTopWreath

theorem canonicalWreath_injective : Function.Injective (C.canonicalWreath e c hc) :=
  (PermutationalWreathProduct.transport e c hc).injective.comp C.actualTopWreath_injective

@[simp] theorem canonicalWreath_top (u : U) :
    (C.canonicalWreath e c hc u).right=e (C.top.rangeRestrict u) := rfl
end SymmetricSubgroupAsymptotics.ProductBlockFrame
