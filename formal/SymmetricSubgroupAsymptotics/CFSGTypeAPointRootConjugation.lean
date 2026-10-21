import SymmetricSubgroupAsymptotics.CFSGTypeAProjectivePointRoots

/-! Exact conjugacy of the original PSL point-root groups by original
SL matrices. The form changes contragrediently on the same vector space;
no abstract automorphism recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeAProjectivePointRoots
open Module LinearMap Matrix
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

def pointFormsCongr (e : (n→F)≃ₗ[F](n→F)) (v : n→F) :
    pointForms v≃ₗ[F]pointForms (e v) where
  toFun f := ⟨f.val.comp e.symm.toLinearMap,by
    change f.val (e.symm (e v))=0
    rw [e.symm_apply_apply]
    exact f.property⟩
  invFun f := ⟨f.val.comp e.toLinearMap,by
    change f.val (e v)=0
    exact f.property⟩
  left_inv f := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    exact congrArg f.val (e.symm_apply_apply x)
  right_inv f := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    exact congrArg f.val (e.apply_symm_apply x)
  map_add' f g := by apply Subtype.ext;apply LinearMap.ext;intro x;rfl
  map_smul' c f := by apply Subtype.ext;apply LinearMap.ext;intro x;rfl

theorem transvectionSL_conjugate (A : SL (F:=F) (n:=n))
    {f : Dual F (n→F)} {v : n→F} (hf : f v=0) :
    A*transvectionSL hf*A⁻¹=
      transvectionSL (show (f.comp A.toLin'.symm.toLinearMap) (A.toLin' v)=0 by
        simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
          using hf) := by
  apply Matrix.SpecialLinearGroup.toLin'_injective
  rw [map_mul,map_mul,map_inv]
  apply LinearEquiv.ext
  intro x
  change A.toLin' ((transvectionSL hf).toLin' (A.toLin'.symm x))=
    (transvectionSL (show (f.comp A.toLin'.symm.toLinearMap) (A.toLin' v)=0 by
      simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
        using hf)).toLin' x
  simp only [transvectionSL_apply,map_add,map_smul,LinearEquiv.apply_symm_apply,
    LinearMap.comp_apply,LinearEquiv.coe_coe]

theorem pointRootHom_conjugate (A : SL (F:=F) (n:=n)) (v : n→F)
    (f : Multiplicative (pointForms v)) :
    projection A*pointRootHom v f*(projection A)⁻¹=
      pointRootHom (A.toLin' v)
        (Multiplicative.ofAdd (pointFormsCongr A.toLin' v f.toAdd)) := by
  change projection A*projection (transvectionSL f.toAdd.property)*(projection A)⁻¹=_
  rw [←map_inv,←map_mul,←map_mul,transvectionSL_conjugate]
  rfl

theorem pointRoot_map_conjugate (A : SL (F:=F) (n:=n)) (v : n→F) :
    (pointRoot v).map (MulAut.conj (projection A)).toMonoidHom=pointRoot (A.toLin' v) := by
  let e := pointFormsCongr A.toLin' v
  ext x
  constructor
  · rintro ⟨y,⟨f,rfl⟩,rfl⟩
    refine ⟨Multiplicative.ofAdd (e f.toAdd),?_⟩
    exact (pointRootHom_conjugate A v f).symm
  · rintro ⟨f,rfl⟩
    refine ⟨pointRootHom v (Multiplicative.ofAdd (e.symm f.toAdd)),⟨_,rfl⟩,?_⟩
    change projection A*pointRootHom v (Multiplicative.ofAdd (e.symm f.toAdd))*
      (projection A)⁻¹=pointRootHom (A.toLin' v) f
    rw [pointRootHom_conjugate]
    exact congrArg (fun t => pointRootHom (A.toLin' v) (Multiplicative.ofAdd t))
      (e.apply_symm_apply f.toAdd)

end SymmetricSubgroupAsymptotics.CFSGTypeAProjectivePointRoots
