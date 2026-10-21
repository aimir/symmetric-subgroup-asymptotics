import SymmetricSubgroupAsymptotics.GeneralThreeTwoPointAction
import SymmetricSubgroupAsymptotics.GeneralThreeTwoActualSubgroupCoverage
import SymmetricSubgroupAsymptotics.ElementaryZModAutomorphismCoordinates
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! Fixed affine point actions over every actual GL3(2) subgroup. Literal
linear conjugacy transports the SAME translations and original8points. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.BinaryThreeAffineRowActions

abbrev Vector := Fin 3 → ZMod 2
abbrev Translation := Multiplicative Vector
abbrev Linear := GeneralThreeTwoMatrixEncoding.Ambient
abbrev Ambient := Equiv.Perm (Fin 8)

def points : Translation ≃ Fin 8 :=
  Multiplicative.toAdd.trans GeneralThreeTwoPointAction.points

private def leftAction : Translation →* Equiv.Perm Translation where
  toFun v := Equiv.mulLeft v
  map_one' := by
    apply Equiv.ext
    intro w
    exact one_mul w
  map_mul' v w := by
    apply Equiv.ext
    intro z
    exact mul_assoc v w z

def translation : Translation →* Ambient :=
  points.permCongrHom.toMonoidHom.comp leftAction

abbrev linear := GeneralThreeTwoPointAction.action
abbrev automorphism := (ElementaryZModAutomorphismCoordinates.matrixEquiv 2 3).symm

theorem translation_apply (v w : Translation) :
    translation v (points w) = points (v*w) := by
  change points ((Equiv.mulLeft v) (points.symm (points w))) = _
  rw [points.symm_apply_apply]
  rfl

theorem linear_apply (c : Linear) (v : Translation) :
    linear c (points v) = points (automorphism c v) := by
  change GeneralThreeTwoPointAction.action c (GeneralThreeTwoPointAction.points v.toAdd) =
    GeneralThreeTwoPointAction.points ((automorphism c v).toAdd)
  rw [GeneralThreeTwoPointAction.action_apply,
    GeneralThreeTwoPointAction.points.symm_apply_apply]
  apply congrArg GeneralThreeTwoPointAction.points
  simpa only [MulEquiv.apply_symm_apply] using
    ElementaryZModAutomorphismCoordinates.matrixEquiv_apply 2 3 (automorphism c) v.toAdd

/-- The full affine point image with this exact actual linear subgroup. -/
def affine (K : Subgroup Linear) : Subgroup Ambient :=
  translation.range ⊔ K.map linear

def rows (i : Fin 15) : Subgroup Ambient :=
  affine (GeneralThreeTwoActualSubgroupCoverage.rows i)

theorem linear_conjugate_translation (c : Linear) (v : Translation) :
    (MulAut.conj (linear c)) (translation v) = translation (automorphism c v) := by
  have h : linear c * translation v = translation (automorphism c v) * linear c := by
    apply Equiv.ext
    intro z
    obtain ⟨w,rfl⟩ := points.surjective z
    change linear c (translation v (points w)) =
      translation (automorphism c v) (linear c (points w))
    rw [translation_apply,linear_apply,linear_apply,translation_apply,map_mul]
  change linear c * translation v * (linear c)⁻¹ = _
  rw [h]
  group

theorem linear_conjugate_translations (c : Linear) :
    MulAut.conj (linear c) • translation.range = translation.range := by
  change translation.range.map (MulAut.conj (linear c)).toMonoidHom = translation.range
  apply le_antisymm
  · rintro p ⟨q,⟨v,rfl⟩,rfl⟩
    exact ⟨automorphism c v,(linear_conjugate_translation c v).symm⟩
  · rintro p ⟨v,rfl⟩
    obtain ⟨w,rfl⟩ := (automorphism c).surjective v
    exact ⟨translation w,⟨w,rfl⟩,linear_conjugate_translation c w⟩

theorem linear_conjugate_linear_image (c : Linear) (K : Subgroup Linear) :
    MulAut.conj (linear c) • K.map linear = (MulAut.conj c • K).map linear := by
  have h : (MulAut.conj (linear c)).toMonoidHom.comp linear =
      linear.comp (MulAut.conj c).toMonoidHom := by
    apply MonoidHom.ext
    intro k
    change linear c * linear k * (linear c)⁻¹ = linear (c*k*c⁻¹)
    rw [map_mul,map_mul,map_inv]
  change (K.map linear).map (MulAut.conj (linear c)).toMonoidHom =
    (K.map (MulAut.conj c).toMonoidHom).map linear
  rw [Subgroup.map_map,Subgroup.map_map,h]

theorem linear_conjugate_affine (c : Linear) (K : Subgroup Linear) :
    MulAut.conj (linear c) • affine K = affine (MulAut.conj c • K) := by
  rw [affine,Subgroup.smul_sup,linear_conjugate_translations,
    linear_conjugate_linear_image]
  rfl

theorem affine_coverage (K : Subgroup Linear) :
    ∃ i : Fin 15, ∃ c : Ambient, MulAut.conj c • affine K = rows i := by
  obtain ⟨i,c,hc⟩ := GeneralThreeTwoActualSubgroupCoverage.complete K
  refine ⟨i,linear c,?_⟩
  rw [linear_conjugate_affine,hc]
  rfl

end SymmetricSubgroupAsymptotics.BinaryThreeAffineRowActions
end
