import SymmetricSubgroupAsymptotics.CFSGSuzukiDiagonalTorus

/-! The exact action of the original Suzuki torus parameter. Its first
unipotent coordinate is multiplied by the inverse original parameter;
this retains a primitive unit without replacing the field chart. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiTorus
open CFSGSuzukiFieldParameters CFSGSuzukiUnipotent

theorem original_torus_conjugation (m : ℕ) (c : (Field m)ˣ) (a b : Field m) :
    torusElement m c*unipotentElement m a b*(torusElement m c)⁻¹=
      unipotentElement m ((c : Field m)⁻¹*a)
        (((c : Field m)*theta m (c : Field m))⁻¹*b) := by
  have hc : (c : Field m)≠0 := Units.ne_zero c
  have hp : inverseTheta m (c : Field m)≠0 := by
    intro he
    apply hc
    apply (inverseTheta m).injective
    simpa only [map_zero] using he
  let d : (Field m)ˣ := Units.mk0 (torusParameter m (c : Field m)) (mul_ne_zero hc hp)
  have hd : normalizedTorusElement m d=torusElement m c := by
    apply Units.ext
    rw [normalizedTorusElement_coe,torusElement_coe,original_torus_eq_diagonalTorus]
    rfl
  rw [←hd,normalizedTorus_conjugation]
  change unipotentElement m
      (theta m (torusParameter m (c : Field m))*a/torusParameter m (c : Field m)^2)
      (b/theta m (torusParameter m (c : Field m)))=_
  have ht : theta m (torusParameter m (c : Field m))=
      theta m (c : Field m)*(c : Field m) := by
    rw [torusParameter,map_mul,theta_inverseTheta]
  rw [ht,torusParameter]
  congr 1
  · rw [←inverseTheta_square]
    field_simp [hc,hp]
  · rw [div_eq_mul_inv]
    ac_rfl

end SymmetricSubgroupAsymptotics.CFSGSuzukiTorus
