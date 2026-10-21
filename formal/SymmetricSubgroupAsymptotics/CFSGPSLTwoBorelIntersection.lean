import SymmetricSubgroupAsymptotics.CFSGPSLTwoGeometry

/-! The diagonal torus is exactly the original pair-Borel intersection
in PSL2. Passing through the centre quotient uses its actual kernel;
injectivity of the quotient map is never assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoGeometry
open Matrix CFSGTypeASLTwoWeyl CFSGTypeARootTorus CFSGSLTwoUpperRoots
open CFSGPSLTwoRootCoordinates CFSGSLTwoBruhat
variable {F : Type*} [Field F]

theorem sl_torus_upper_entry00 (c : Fˣ) (a : F) :
    (torusHom c*upper a).val 0 0=(c : F) := by
  change ((torus (by decide : (0 : Fin 2)≠1) c).val*(upper a).val) 0 0=(c : F)
  rw [torus_coe]
  simp [Matrix.diagonal_mul]

theorem sl_torus_upper_entry01 (c : Fˣ) (a : F) :
    (torusHom c*upper a).val 0 1=(c : F)*a := by
  change ((torus (by decide : (0 : Fin 2)≠1) c).val*(upper a).val) 0 1=(c : F)*a
  rw [torus_coe]
  simp [Matrix.diagonal_mul]

theorem sl_opposite_entry01 (g : SL2 (F:=F)) :
    (weyl*g*weyl⁻¹).val 0 1= -g.val 1 0 := by
  change ((weyl.val*g.val*(weyl⁻¹).val) : Matrix (Fin 2) (Fin 2) F) 0 1= -g.val 1 0
  rw [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,sl_weyl_coe]
  simp [Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]

theorem sl_borel_inf_opposite_borel :
    borel (F:=F) ⊓ (borel (F:=F)).map (MulAut.conj (weyl (F:=F))).toMonoidHom=
      (torusHom (F:=F)).range := by
  apply le_antisymm
  · rintro g ⟨hg,v,hv,he⟩
    have h01 : g.val 0 1=0 := by
      rw [←he]
      change (weyl*v*weyl⁻¹).val 0 1=0
      rw [sl_opposite_entry01]
      exact neg_eq_zero.mpr hv
    obtain ⟨c,a,hg⟩ := borel_factor g hg
    rw [hg,sl_torus_upper_entry01] at h01
    have ha : a=0 := (mul_eq_zero.mp h01).resolve_left (Units.ne_zero c)
    refine ⟨c,?_⟩
    rw [hg,ha]
    have hu : upper (0 : F)=(1 : SL2 (F:=F)) := (upperHom (F:=F)).map_one
    rw [hu,mul_one]
  · rintro g ⟨c,rfl⟩
    refine ⟨torus_mem_borel c,torusHom c⁻¹,torus_mem_borel c⁻¹,?_⟩
    change weyl*torus (by decide : (0 : Fin 2)≠1) c⁻¹*weyl⁻¹=
      torus (by decide : (0 : Fin 2)≠1) c
    rw [weyl_torus,inv_inv]

theorem map_conjugate_subgroup {A H : Type*} [Group A] [Group H]
    (f : A →* H) (S : Subgroup A) (w : A) :
    (S.map f).map (MulAut.conj (f w)).toMonoidHom=
      (S.map (MulAut.conj w).toMonoidHom).map f := by
  rw [Subgroup.map_map,Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro g
  change f w*f g*(f w)⁻¹=f (w*g*w⁻¹)
  simp only [map_mul,map_inv]

theorem map_inf_of_ker_le_left {A H : Type*} [Group A] [Group H]
    (f : A →* H) (S T : Subgroup A) (hker : f.ker≤S) :
    (S ⊓ T).map f=S.map f ⊓ T.map f := by
  apply le_antisymm (Subgroup.map_inf_le _ _ _)
  rintro y ⟨⟨s,hs,hsy⟩,⟨t,ht,hty⟩⟩
  have hd : s*t⁻¹∈f.ker := by
    change f (s*t⁻¹)=1
    rw [map_mul,map_inv,hsy,hty,mul_inv_cancel]
  have hts : t∈S := by
    have hh := S.mul_mem (S.inv_mem (hker hd)) hs
    simpa [mul_assoc] using hh
  exact ⟨t,⟨hts,ht⟩,hty⟩

theorem projectiveBorel_inf_opposite_borel :
    projectiveBorel (F:=F) ⊓ (projectiveBorel (F:=F)).map
      (MulAut.conj (projectiveWeyl (F:=F))).toMonoidHom=pairTorus (F:=F) := by
  have hk : (projection (F:=F)).ker≤borel (F:=F) := by
    rw [projection,QuotientGroup.ker_mk']
    exact center_le_borel
  change (borel (F:=F)).map projection ⊓ ((borel (F:=F)).map projection).map
    (MulAut.conj (projection (weyl (F:=F)))).toMonoidHom=pairTorus
  rw [map_conjugate_subgroup,←map_inf_of_ker_le_left projection _ _ hk,
    sl_borel_inf_opposite_borel,←MonoidHom.range_comp]
  rfl

end SymmetricSubgroupAsymptotics.CFSGPSLTwoGeometry
