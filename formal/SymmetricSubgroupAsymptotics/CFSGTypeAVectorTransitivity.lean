import SymmetricSubgroupAsymptotics.CFSGTypeAProjectivePointRoots
import SymmetricSubgroupAsymptotics.CFSGTypeARootTorus

/-! Literal determinant-one normalization of a nonzero coordinate vector.
A pivot shear and an actual two-coordinate torus suffice; no projective
vector or arbitrary GL determinant is substituted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTypeAVectorTransitivity
open Matrix CFSGTypeAProjectivePointRoots CFSGTypeARootTorus
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

private theorem normalize_nonzero_pivot (b c : n) (hbc : b≠c)
    (v : n→F) (hv : v b≠0) :
    ∃ g : Matrix.SpecialLinearGroup n F,g.toLin' v=Pi.single b 1 := by
  let u : n→F := fun j => if j=b then 0 else -(v j/v b)
  have hu : (LinearMap.proj b : (n→F)→ₗ[F]F) u=0 := by simp [u]
  let a : Matrix.SpecialLinearGroup n F := transvectionSL hu
  have ha : a.toLin' v=Pi.single b (v b) := by
    rw [show a.toLin' v=v+v b • u from transvectionSL_apply hu v]
    ext j
    by_cases hj : j=b
    · subst j
      simp [u]
    · simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,u,if_neg hj,
        Pi.single_eq_of_ne hj]
      field_simp [hv]
      <;> ring
  let d : Fˣ := (Units.mk0 (v b) hv)⁻¹
  let t : Matrix.SpecialLinearGroup n F := torus hbc d
  have ht : t.toLin' (Pi.single b (v b))=Pi.single b 1 := by
    change Matrix.toLin' t.val (Pi.single b (v b))=_
    rw [Matrix.toLin'_apply,show t.val=Matrix.diagonal
      (fun k => if k=b then (d : F) else if k=c then (d : F)⁻¹ else 1) from torus_coe hbc d,
      Matrix.diagonal_mulVec_single]
    congr 1
    simp [d,hv]
  refine ⟨t*a,?_⟩
  rw [map_mul,LinearEquiv.mul_apply,ha,ht]

theorem exists_normalize (b c : n) (hbc : b≠c) (v : n→F) (hv : v≠0) :
    ∃ g : Matrix.SpecialLinearGroup n F,g.toLin' v=Pi.single b 1 := by
  by_cases hb : v b≠0
  · exact normalize_nonzero_pivot b c hbc v hb
  have hb0 : v b=0 := not_ne_iff.mp hb
  obtain ⟨j,hj⟩ : ∃ j,v j≠0 := by
    by_contra h
    apply hv
    funext j
    exact not_ne_iff.mp (fun hj => h ⟨j,hj⟩)
  have hjb : j≠b := by rintro rfl; exact hj hb0
  have hz : (LinearMap.proj j : (n→F)→ₗ[F]F) (Pi.single b (1 : F))=0 := by
    change (Pi.single b (1 : F) : n→F) j=0
    simp [Pi.single_apply,hjb,Ne.symm hjb]
  let a : Matrix.SpecialLinearGroup n F := transvectionSL hz
  have hp : (a.toLin' v) b≠0 := by
    rw [show a.toLin' v=v+v j • Pi.single b 1 from transvectionSL_apply hz v]
    simpa only [Pi.add_apply,Pi.smul_apply,Pi.single_eq_same,smul_eq_mul,
      mul_one,hb0,zero_add] using hj
  obtain ⟨g,hg⟩ := normalize_nonzero_pivot b c hbc (a.toLin' v) hp
  refine ⟨g*a,?_⟩
  rw [map_mul,LinearEquiv.mul_apply]
  exact hg

theorem exists_map_nonzero (b c : n) (hbc : b≠c) (v w : n→F)
    (hv : v≠0) (hw : w≠0) :
    ∃ g : Matrix.SpecialLinearGroup n F,g.toLin' v=w := by
  obtain ⟨a,ha⟩ := exists_normalize b c hbc v hv
  obtain ⟨d,hd⟩ := exists_normalize b c hbc w hw
  refine ⟨d⁻¹*a,?_⟩
  rw [map_mul,map_inv,LinearEquiv.mul_apply,ha,←hd,LinearEquiv.coe_inv,LinearEquiv.symm_apply_apply]

end SymmetricSubgroupAsymptotics.CFSGTypeAVectorTransitivity
