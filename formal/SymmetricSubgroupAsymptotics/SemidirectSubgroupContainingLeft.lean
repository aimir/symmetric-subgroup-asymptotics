import SymmetricSubgroupAsymptotics.IrreducibleAbelianSemidirectOrdinaryGenerators
import SymmetricSubgroupAsymptotics.CoprimeNilpotentProductGenerators

/-! A subgroup of an actual split group that contains the entire left
factor is precisely the split preimage of its actual right image. This
identification is proved; splitting is not assumed for an arbitrary
extension. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.SemidirectSubgroupContainingLeft
open SemidirectProduct

section Group
variable {V H : Type} [Group V] [Group H] (φ : H →* MulAut V)
    (N : Subgroup (V ⋊[φ] H))
    (hleft : (inl : V →* V ⋊[φ] H).range ≤ N)

include hleft

theorem mem_iff_right_mem (g : V ⋊[φ] H) :
    g ∈ N ↔ g.right ∈ N.map (rightHom : V ⋊[φ] H →* H) := by
  constructor
  · intro hg
    exact ⟨g,hg,rfl⟩
  · rintro ⟨x,hx,he⟩
    have hxinl : (inl x.left : V ⋊[φ] H) ∈ N := hleft ⟨x.left,rfl⟩
    have hxright : (inr x.right : V ⋊[φ] H) ∈ N := by
      have hh := N.mul_mem (N.inv_mem hxinl) hx
      have heq : (inl x.left : V ⋊[φ] H)⁻¹ * x = inr x.right :=
        (congrArg (fun z : V ⋊[φ] H => (inl x.left)⁻¹ * z)
          (inl_left_mul_inr_right x).symm).trans (inv_mul_cancel_left _ _)
      exact heq ▸ hh
    have hgright : (inr g.right : V ⋊[φ] H) ∈ N := by
      change x.right = g.right at he
      rw [← he]
      exact hxright
    rw [← inl_left_mul_inr_right g]
    exact N.mul_mem (hleft ⟨g.left,rfl⟩) hgright

def splitEquiv : N ≃*
    V ⋊[φ.comp (N.map (rightHom : V ⋊[φ] H →* H)).subtype]
      (N.map (rightHom : V ⋊[φ] H →* H)) where
  toFun g := ⟨g.val.left,⟨g.val.right,⟨g.val,g.property,rfl⟩⟩⟩
  invFun g := ⟨⟨g.left,g.right.val⟩,
    (mem_iff_right_mem φ N hleft ⟨g.left,g.right.val⟩).mpr g.right.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end Group

theorem genRank_le_image_add_one
    {V H : Type} [CommGroup V] [Finite V] [Nontrivial V] [Group H] [Finite H]
    (φ : H →* MulAut V) (N : Subgroup (V ⋊[φ] H))
    (hleft : (inl : V →* V ⋊[φ] H).range ≤ N)
    (hirr : IrreducibleAbelianSemidirect.Irreducible
      (φ.comp (N.map (rightHom : V ⋊[φ] H →* H)).subtype)) :
    MarkedC4.genRank N ≤ MarkedC4.genRank (N.map (rightHom : V ⋊[φ] H →* H))+1 := by
  let E := N.map (rightHom : V ⋊[φ] H →* H)
  let ψ := φ.comp E.subtype
  letI : Finite (V ⋊[φ] H) := Finite.of_equiv (V × H) equivProd.symm
  letI : Finite (V ⋊[ψ] E) := Finite.of_equiv (V × E) equivProd.symm
  rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv (splitEquiv φ N hleft)]
  exact IrreducibleAbelianSemidirectOrdinaryGenerators.genRank_le_complement_add_one ψ hirr

end SymmetricSubgroupAsymptotics.SemidirectSubgroupContainingLeft
