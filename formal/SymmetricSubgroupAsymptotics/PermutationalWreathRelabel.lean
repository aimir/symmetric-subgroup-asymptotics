import SymmetricSubgroupAsymptotics.ActualFullWreathFamily

/-! Literal relabelling of the local group, top group and block points.
It preserves the complete full-component family and the actual product
point action. This is the transport used in the labelled block cover. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PermutationalWreathRelabel
open PermutationalWreathProduct ActualFullWreathFamily

variable {D D' Q Q' I I' : Type} [Group D] [Group D'] [Group Q] [Group Q']
    [MulAction Q I] [MulAction Q' I']
    (eD : D ≃* D') (eQ : Q ≃* Q') (eI : I ≃ I')
    (hQ : ∀ q i,eI (q • i)=eQ q • eI i)

include hQ in
theorem symm_smul (q : Q) (j : I') :
    eI.symm (eQ q • j)=q • eI.symm j := by
  apply eI.injective
  rw [eI.apply_symm_apply,hQ,eI.apply_symm_apply]

def relabel : PermutationalWreathProduct D Q I ≃* PermutationalWreathProduct D' Q' I' where
  toFun w := ⟨fun j => eD (w.left (eI.symm j)),eQ w.right⟩
  invFun w := ⟨fun i => eD.symm (w.left (eI i)),eQ.symm w.right⟩
  left_inv w := by
    apply PermutationalWreathProduct.ext
    · funext i
      exact (congrArg eD.symm (congrArg (fun x => eD (w.left x))
        (eI.symm_apply_apply i))).trans (eD.symm_apply_apply (w.left i))
    · exact eQ.symm_apply_apply w.right
  right_inv w := by
    apply PermutationalWreathProduct.ext
    · funext j
      exact (congrArg eD (congrArg (fun x => eD.symm (w.left x))
        (eI.apply_symm_apply j))).trans (eD.apply_symm_apply (w.left j))
    · exact eQ.apply_symm_apply w.right
  map_mul' a b := by
    apply PermutationalWreathProduct.ext
    · funext j
      change eD (a.left (eI.symm j)*b.left (a.right⁻¹ • eI.symm j))=
        eD (a.left (eI.symm j))*eD (b.left (eI.symm ((eQ a.right)⁻¹ • j)))
      rw [map_mul,←map_inv,symm_smul eQ eI hQ]
    · exact eQ.map_mul a.right b.right

@[simp] theorem relabel_left (w : PermutationalWreathProduct D Q I) (j : I') :
    (relabel eD eQ eI hQ w).left j=eD (w.left (eI.symm j)) := rfl

@[simp] theorem relabel_right (w : PermutationalWreathProduct D Q I) :
    (relabel eD eQ eI hQ w).right=eQ w.right := rfl

section PointAction
variable {Y Y' : Type} [MulAction D Y] [MulAction D' Y']
    (eY : Y ≃ Y') (hD : ∀ d y,eY (d • y)=eD d • eY y)

include hD in
theorem product_equivariant (w : PermutationalWreathProduct D Q I) (p : Y×I) :
    (Equiv.prodCongr eY eI) (w • p)=
      relabel eD eQ eI hQ w • (Equiv.prodCongr eY eI p) := by
  change (eY (w.left (w.right • p.2) • p.1),eI (w.right • p.2))=
    (eD (w.left (eI.symm (eQ w.right • eI p.2))) • eY p.1,eQ w.right • eI p.2)
  apply Prod.ext
  · change eY (w.left (w.right • p.2) • p.1)=
      eD (w.left (eI.symm (eQ w.right • eI p.2))) • eY p.1
    rw [←hQ w.right p.2,eI.symm_apply_apply,hD]
  · exact hQ w.right p.2
end PointAction

def family (L : Family D Q I) : Family D' Q' I' := by
  refine ⟨L.val.map (relabel eD eQ eI hQ).toMonoidHom,?_,?_⟩
  · apply top_unique
    intro q' _
    obtain ⟨g,hg⟩ := top_surjective L (eQ.symm q')
    refine ⟨relabel eD eQ eI hQ g.val,⟨g.val,g.property,rfl⟩,?_⟩
    exact (congrArg eQ hg).trans (eQ.apply_symm_apply q')
  · intro j d'
    obtain ⟨g,hfix,hcoord⟩ := L.property.2 (eI.symm j) (eD.symm d')
    refine ⟨⟨relabel eD eQ eI hQ g.val,⟨g.val,g.property,rfl⟩⟩,?_,?_⟩
    · change eQ g.val.right • j=j
      calc
        _=eI (g.val.right • eI.symm j) := by
          simpa only [eI.apply_symm_apply] using (hQ g.val.right (eI.symm j)).symm
        _=j := (congrArg eI hfix).trans (eI.apply_symm_apply j)
    · exact (congrArg eD hcoord).trans (eD.apply_symm_apply d')

theorem family_injective : Function.Injective (family eD eQ eI hQ) := by
  intro L M h
  apply Subtype.ext
  exact Subgroup.map_injective (relabel eD eQ eI hQ).injective
    (congrArg (fun H : Family D' Q' I' => H.val) h)

end SymmetricSubgroupAsymptotics.PermutationalWreathRelabel
