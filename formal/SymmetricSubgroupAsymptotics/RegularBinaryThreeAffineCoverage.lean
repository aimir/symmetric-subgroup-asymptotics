import SymmetricSubgroupAsymptotics.BinaryThreeAffineRowActions
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightCoordinateAction
import SymmetricSubgroupAsymptotics.OrbitProfileAssembly

/-! Every actual regular-normal E8 profile has one of fifteen fixed affine
point actions. No primitiveness or irreducibility premise is used; the
translation chart and original point action are retained throughout. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.RegularBinaryThreeAffineCoverage
open BinaryThreeAffineRowActions

variable {X : Type} {S : Subgroup (Equiv.Perm X)}
  (P : PrimitiveAffineProfile S X) (x : X) (a : P.V ≃* Translation)

def pointChart : X ≃ Fin 8 :=
  (P.pointEquiv x).symm.trans (a.toEquiv.trans points)

def relabelHom : S →* Ambient :=
  (pointChart P x a).permCongrHom.toMonoidHom.comp S.subtype

theorem pointChart_translation (v : P.V) :
    pointChart P x a (P.pointEquiv x v) = points (a v) := by
  simp only [pointChart,Equiv.trans_apply,Equiv.symm_apply_apply]
  rfl

theorem relabel_apply (g : S) (y : X) :
    relabelHom P x a g (pointChart P x a y) = pointChart P x a (g.val y) := by
  change pointChart P x a (g.val ((pointChart P x a).symm (pointChart P x a y))) = _
  rw [Equiv.symm_apply_apply]

theorem relabel_translation (v : P.V) :
    relabelHom P x a v.val = translation (a v) := by
  apply Equiv.ext
  intro z
  obtain ⟨w,rfl⟩ := (a.toEquiv.trans points).surjective z
  change relabelHom P x a v.val (points (a w)) = translation (a v) (points (a w))
  rw [←pointChart_translation P x a w,relabel_apply]
  have hvw : (v.val : S) • P.pointEquiv x w = P.pointEquiv x (v*w) :=
    (mul_smul (v.val : S) (w.val : S) x).symm
  change pointChart P x a ((v.val : S) • P.pointEquiv x w) = _
  rw [hvw,pointChart_translation,map_mul,pointChart_translation,translation_apply]

private theorem stabilizer_translation (k : P.complement x) (v : P.V) :
    (k.val : S) • P.pointEquiv x v =
      P.pointEquiv x (P.complementAction x k v) := by
  change (k.val : S) • ((v.val : S) • x) =
    ((k.val : S) * (v.val : S) * (k.val : S)⁻¹) • x
  have hk : (k.val : S)⁻¹ • x = x := by
    calc
      (k.val : S)⁻¹ • x = (k.val : S)⁻¹ • ((k.val : S) • x) :=
        congrArg ((k.val : S)⁻¹ • ·) k.property.symm
      _ = x := inv_smul_smul _ _
  rw [mul_smul,mul_smul,hk]

theorem coordinate_automorphism (k : P.complement x) (v : P.V) :
    automorphism (P.complementCoordinateMap x a k) (a v) =
      a (P.complementAction x k v) := by
  change ((ElementaryZModAutomorphismCoordinates.matrixEquiv 2 3).symm
    (ElementaryZModAutomorphismCoordinates.matrixEquiv 2 3
      ((MulAut.congr a) (P.complementAction x k)))) (a v) = _
  rw [MulEquiv.symm_apply_apply]
  change a (P.complementAction x k (a.symm (a v))) = _
  rw [a.symm_apply_apply]

theorem relabel_complement (k : P.complement x) :
    relabelHom P x a k.val = linear (P.complementCoordinateMap x a k) := by
  apply Equiv.ext
  intro z
  obtain ⟨w,rfl⟩ := (a.toEquiv.trans points).surjective z
  change relabelHom P x a k.val (points (a w)) = _
  rw [←pointChart_translation P x a w,relabel_apply]
  change pointChart P x a ((k.val : S) • P.pointEquiv x w) = _
  rw [stabilizer_translation,pointChart_translation]
  change points (a (P.complementAction x k w)) =
    linear (P.complementCoordinateMap x a k) (points (a w))
  rw [linear_apply,coordinate_automorphism]

theorem image_eq_affine :
    (relabelHom P x a).range = affine (P.complementCoordinateMap x a).range := by
  apply le_antisymm
  · rintro p ⟨g,rfl⟩
    obtain ⟨u,rfl⟩ := (P.semidirectEquiv x).surjective g
    have hu : P.semidirectEquiv x u = u.left.val*u.right.val := rfl
    rw [hu,map_mul,relabel_translation,relabel_complement]
    exact (affine (P.complementCoordinateMap x a).range).mul_mem
      ((show translation.range ≤ affine (P.complementCoordinateMap x a).range from le_sup_left)
        ⟨a u.left,rfl⟩)
      ((show (P.complementCoordinateMap x a).range.map linear ≤
          affine (P.complementCoordinateMap x a).range from le_sup_right)
        ⟨P.complementCoordinateMap x a u.right,⟨u.right,rfl⟩,rfl⟩)
  · change translation.range ⊔ (P.complementCoordinateMap x a).range.map linear ≤ _
    refine sup_le ?_ ?_
    · rintro p ⟨v,rfl⟩
      refine ⟨(a.symm v).val,?_⟩
      rw [relabel_translation,a.apply_symm_apply]
    · rintro p ⟨m,⟨k,rfl⟩,rfl⟩
      exact ⟨k.val,relabel_complement P x a k⟩

theorem relabel_eq_affine :
    relabelSubgroup (pointChart P x a) S = affine (P.complementCoordinateMap x a).range := by
  have h : (relabelHom P x a).range = relabelSubgroup (pointChart P x a) S := by
    ext p
    constructor
    · rintro ⟨g,rfl⟩
      exact ⟨g.val,g.property,rfl⟩
    · rintro ⟨g,hg,rfl⟩
      exact ⟨⟨g,hg⟩,rfl⟩
  exact h.symm.trans (image_eq_affine P x a)

include P x a in
/-- The original permutation group has an actual point chart to a fixed
row, even if its point-stabilizer action has proper invariant subspaces. -/
theorem complete : ∃ i : Fin 15, ∃ c : X ≃ Fin 8,
    relabelSubgroup c S = BinaryThreeAffineRowActions.rows i := by
  obtain ⟨i,c,hc⟩ := affine_coverage (P.complementCoordinateMap x a).range
  refine ⟨i,(pointChart P x a).trans c,?_⟩
  rw [←relabelSubgroup_trans,relabel_eq_affine]
  exact hc

end SymmetricSubgroupAsymptotics.RegularBinaryThreeAffineCoverage
end
