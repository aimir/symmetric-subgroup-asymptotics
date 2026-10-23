import Mathlib.GroupTheory.SemidirectProduct

/-! An actual subgroup containing the whole kernel of a semidirect
product is itself the semidirect product with its ACTUAL projected top.
If its kernel intersection is trivial, the same projection is injective.
No splitting or subgroup class comparison is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SemidirectSubgroupOverKernel

variable {N H : Type*} [Group N] [Group H] (φ : H →* MulAut N)

abbrev Projected (L : Subgroup (N ⋊[φ] H)) : Subgroup H :=
  L.map SemidirectProduct.rightHom

def overKernelEquiv (L : Subgroup (N ⋊[φ] H))
    (hN : ∀ n : N, SemidirectProduct.inl n ∈ L) :
    L ≃* N ⋊[φ.comp (Projected φ L).subtype] Projected φ L where
  toFun x := ⟨x.val.left,⟨x.val.right,⟨x.val,x.property,rfl⟩⟩⟩
  invFun x := ⟨⟨x.left,x.right.val⟩,by
    obtain ⟨y,hy,he⟩ := x.right.property
    change y.right=x.right.val at he
    have hmul := L.mul_mem (hN (x.left*y.left⁻¹)) hy
    have heq : (SemidirectProduct.inl (x.left*y.left⁻¹) : N ⋊[φ] H)*y =
        ⟨x.left,x.right.val⟩ := by
      apply SemidirectProduct.ext
      · change (x.left*y.left⁻¹)*φ 1 y.left=x.left
        simp only [map_one,MulAut.one_apply,mul_assoc,inv_mul_cancel,mul_one]
      · change 1*y.right=x.right.val
        simpa only [one_mul] using he
    rw [heq] at hmul
    exact hmul⟩
  left_inv _x := rfl
  right_inv _x := rfl
  map_mul' _x _y := by apply SemidirectProduct.ext <;> rfl

theorem rightHom_injective_of_comap_bot (L : Subgroup (N ⋊[φ] H))
    (hK : L.comap (SemidirectProduct.inl : N →* N ⋊[φ] H)=⊥) :
    Function.Injective ((SemidirectProduct.rightHom : (N ⋊[φ] H) →* H).comp L.subtype) := by
  let f : L →* H := (SemidirectProduct.rightHom : (N ⋊[φ] H) →* H).comp L.subtype
  change Function.Injective f
  apply f.ker_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro x hx
  change x.val.right=1 at hx
  have he : (SemidirectProduct.inl x.val.left : N ⋊[φ] H)=x.val := by
    apply SemidirectProduct.ext
    · rfl
    · exact hx.symm
  have hleft : x.val.left ∈ L.comap (SemidirectProduct.inl : N →* N ⋊[φ] H) := by
    change SemidirectProduct.inl x.val.left ∈ L
    rw [he]
    exact x.property
  rw [hK] at hleft
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  apply SemidirectProduct.ext
  · exact Subgroup.mem_bot.mp hleft
  · exact hx

end SymmetricSubgroupAsymptotics.SemidirectSubgroupOverKernel
