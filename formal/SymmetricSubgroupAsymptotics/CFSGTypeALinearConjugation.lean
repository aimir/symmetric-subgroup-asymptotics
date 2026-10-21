import SymmetricSubgroupAsymptotics.CFSGTypeAPointRootConjugation
import Mathlib.LinearAlgebra.SpecialLinearGroup

/-! Every original linear change of basis induces an actual automorphism
of the original SL and PSL models. The determinant of the change of
basis is unrestricted; conjugation preserves determinant one. The
original transvection vectors/forms and point-root groups are transported
with their exact contragredient parameters. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeAProjectivePointRoots
open Module LinearMap Matrix
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

def linearConjugation (e : (n→F)≃ₗ[F](n→F)) : MulAut (SL (F:=F) (n:=n)) :=
  Matrix.SpecialLinearGroup.toLin'_equiv.trans
    ((_root_.SpecialLinearGroup.congr_linearEquiv e).trans
      Matrix.SpecialLinearGroup.toLin'_equiv.symm)

theorem linearConjugation_apply (e : (n→F)≃ₗ[F](n→F)) (A : SL (F:=F) (n:=n)) (x : n→F) :
    (linearConjugation e A).toLin' x=e (A.toLin' (e.symm x)) := by
  let E : SL (F:=F) (n:=n)≃*_root_.SpecialLinearGroup F (n→F) :=
    Matrix.SpecialLinearGroup.toLin'_equiv
  have h : E (linearConjugation e A)=_root_.SpecialLinearGroup.congr_linearEquiv e (E A) :=
    E.apply_symm_apply _
  exact congrArg (fun B : _root_.SpecialLinearGroup F (n→F) => B x) h

theorem linearConjugation_transvection (e : (n→F)≃ₗ[F](n→F))
    {f : Dual F (n→F)} {v : n→F} (hf : f v=0) :
    linearConjugation e (transvectionSL hf)=
      transvectionSL (show (f.comp e.symm.toLinearMap) (e v)=0 by
        simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,e.symm_apply_apply] using hf) := by
  apply Matrix.SpecialLinearGroup.toLin'_injective
  apply LinearEquiv.ext
  intro x
  rw [linearConjugation_apply,transvectionSL_apply,transvectionSL_apply]
  simp only [map_add,map_smul,e.apply_symm_apply,LinearMap.comp_apply,LinearEquiv.coe_coe]

private theorem linearConjugation_map_center (e : (n→F)≃ₗ[F](n→F)) :
    (Subgroup.center (SL (F:=F) (n:=n))).map (linearConjugation e).toMonoidHom=
      Subgroup.center (SL (F:=F) (n:=n)) := by
  apply le_antisymm
  · rintro x ⟨y,hy,rfl⟩
    exact (Subgroup.centerCongr (linearConjugation e) ⟨y,hy⟩).property
  · intro x hx
    refine ⟨(linearConjugation e).symm x,?_,(linearConjugation e).apply_symm_apply x⟩
    exact ((Subgroup.centerCongr (linearConjugation e)).symm ⟨x,hx⟩).property

def projectiveLinearConjugation (e : (n→F)≃ₗ[F](n→F)) : MulAut (PSL (F:=F) (n:=n)) :=
  QuotientGroup.congr (Subgroup.center (SL (F:=F) (n:=n)))
    (Subgroup.center (SL (F:=F) (n:=n))) (linearConjugation e) (linearConjugation_map_center e)

theorem projectiveLinearConjugation_apply (e : (n→F)≃ₗ[F](n→F)) (A : SL (F:=F) (n:=n)) :
    projectiveLinearConjugation e (projection A)=projection (linearConjugation e A) := rfl

theorem pointRootHom_linearConjugation (e : (n→F)≃ₗ[F](n→F)) (v : n→F)
    (f : Multiplicative (pointForms v)) :
    projectiveLinearConjugation e (pointRootHom v f)=
      pointRootHom (e v) (Multiplicative.ofAdd (pointFormsCongr e v f.toAdd)) := by
  change projectiveLinearConjugation e (projection (transvectionSL f.toAdd.property))=_
  rw [projectiveLinearConjugation_apply,linearConjugation_transvection]
  rfl

theorem pointRoot_map_linearConjugation (e : (n→F)≃ₗ[F](n→F)) (v : n→F) :
    (pointRoot v).map (projectiveLinearConjugation e).toMonoidHom=pointRoot (e v) := by
  let d := pointFormsCongr e v
  ext x
  constructor
  · rintro ⟨y,⟨f,rfl⟩,rfl⟩
    refine ⟨Multiplicative.ofAdd (d f.toAdd),?_⟩
    exact (pointRootHom_linearConjugation e v f).symm
  · rintro ⟨f,rfl⟩
    refine ⟨pointRootHom v (Multiplicative.ofAdd (d.symm f.toAdd)),⟨_,rfl⟩,?_⟩
    change projectiveLinearConjugation e (pointRootHom v (Multiplicative.ofAdd (d.symm f.toAdd)))=
      pointRootHom (e v) f
    rw [pointRootHom_linearConjugation]
    exact congrArg (fun t => pointRootHom (e v) (Multiplicative.ofAdd t))
      (d.apply_symm_apply f.toAdd)

end SymmetricSubgroupAsymptotics.CFSGTypeAProjectivePointRoots
