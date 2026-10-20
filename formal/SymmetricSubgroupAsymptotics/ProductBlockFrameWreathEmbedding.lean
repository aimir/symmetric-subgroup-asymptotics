import SymmetricSubgroupAsymptotics.ProductBlockFrameGenerators
import SymmetricSubgroupAsymptotics.PermutationalWreathProduct

/-! The full physical coordinate action embeds an original product-frame
subgroup in its permutational wreath, retaining the literal top map. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame
variable {X I F : Type} {U : Subgroup (Equiv.Perm X)}
  (C : ProductBlockFrame U I F)

private def coordinates : U →* Equiv.Perm (I × F) :=
  C.frame.symm.permCongrHom.toMonoidHom.comp U.subtype

private theorem coordinates_pair (u : U) (i : I) (x : F) :
    coordinates C u (i,x) = (C.top u i,(coordinates C u (i,x)).2) :=
  Prod.ext (C.intertwine u (i,x)) rfl

private def localPerm (u : U) (i : I) : Equiv.Perm F where
  toFun x := (coordinates C u ((C.top u)⁻¹ i,x)).2
  invFun x := (coordinates C u⁻¹ (i,x)).2
  left_inv x := by
    have h := congrArg (fun z => (coordinates C u⁻¹ z).2)
      (coordinates_pair C u ((C.top u)⁻¹ i) x)
    rw [map_inv] at h
    have hi : C.top u ((C.top u)⁻¹ i) = i := (C.top u).apply_symm_apply i
    rw [hi] at h
    simpa only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] using h.symm
  right_inv x := by
    have h := congrArg (fun z => (coordinates C u z).2)
      (coordinates_pair C u⁻¹ i x)
    rw [map_inv] at h
    simpa only [map_inv, Equiv.Perm.inv_def, Equiv.apply_symm_apply] using h.symm

/-- Destination-indexed local maps together with the exact original top. -/
def wreathEmbedding : U →*
    PermutationalWreathProduct (Equiv.Perm F) (Equiv.Perm I) I where
  toFun u := ⟨localPerm C u,C.top u⟩
  map_one' := by
    apply PermutationalWreathProduct.ext
    · funext i
      apply Equiv.ext
      intro x
      change (coordinates C 1 ((C.top 1)⁻¹ i,x)).2 = x
      rw [map_one,map_one]
      rfl
    · exact map_one C.top
  map_mul' u v := by
    apply PermutationalWreathProduct.ext
    · funext i
      apply Equiv.ext
      intro x
      change (coordinates C (u*v) ((C.top (u*v))⁻¹ i,x)).2 =
        (coordinates C u ((C.top u)⁻¹ i,
          (coordinates C v ((C.top v)⁻¹ ((C.top u)⁻¹ i),x)).2)).2
      rw [map_mul,map_mul]
      change (coordinates C u (coordinates C v
        ((C.top v)⁻¹ ((C.top u)⁻¹ i),x))).2 = _
      rw [coordinates_pair C v]
      have h : C.top v ((C.top v)⁻¹ ((C.top u)⁻¹ i)) = (C.top u)⁻¹ i :=
        (C.top v).apply_symm_apply _
      rw [h]
    · exact map_mul C.top u v

@[simp] theorem wreathEmbedding_top (u : U) :
    (C.wreathEmbedding u).right = C.top u := rfl

theorem wreathEmbedding_injective : Function.Injective C.wreathEmbedding := by
  intro u v huv
  have ht : C.top u = C.top v := congrArg PermutationalWreathProduct.right huv
  have hl : localPerm C u = localPerm C v := congrArg PermutationalWreathProduct.left huv
  apply Subtype.ext
  apply C.frame.symm.permCongrHom.injective
  apply Equiv.ext
  rintro ⟨i,x⟩
  apply Prod.ext
  · exact (C.intertwine u (i,x)).trans
      ((congrArg (fun p : Equiv.Perm I => p i) ht).trans ((C.intertwine v (i,x)).symm))
  · have h := congrArg (fun f : I → Equiv.Perm F => f (C.top u i) x) hl
    change (coordinates C u ((C.top u)⁻¹ (C.top u i),x)).2 =
      (coordinates C v ((C.top v)⁻¹ (C.top u i),x)).2 at h
    rw [ht] at h
    simpa only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] using h

end SymmetricSubgroupAsymptotics.ProductBlockFrame
