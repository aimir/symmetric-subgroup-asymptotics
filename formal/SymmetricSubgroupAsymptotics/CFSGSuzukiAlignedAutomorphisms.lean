import SymmetricSubgroupAsymptotics.CFSGSuzukiBorelIntersection

/-! Original-group automorphisms can be inner-adjusted to preserve
the actual U, opposite U and diagonal torus simultaneously. These are
subgroup-map equalities, suitable for restriction to the literal U. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiAlignedAutomorphisms
open CFSGSuzukiSylowOfNormalizer CFSGSuzukiGoodSylow CFSGSuzukiSylowAlignment
open CFSGSuzukiBorelIntersection

def modelOppositeUnipotent (m : ℕ) : Subgroup (ActualGroup m) :=
  (modelUnipotent m).map (MulAut.conj (modelWeyl m)).toMonoidHom

theorem opposite_normalizer (m : ℕ) :
    Subgroup.normalizer (modelOppositeUnipotent m : Set (ActualGroup m))=
      (modelBorel m).map (MulAut.conj (modelWeyl m)).toMonoidHom := by
  rw [←model_normalizer_eq_borel]
  exact (Subgroup.map_normalizer_eq_of_bijective (modelUnipotent m)
    (MulAut.conj (modelWeyl m)).bijective).symm

theorem pair_normalizer_eq_torus (m : ℕ) :
    Subgroup.normalizer (modelUnipotent m : Set (ActualGroup m)) ⊓
      Subgroup.normalizer (modelOppositeUnipotent m : Set (ActualGroup m))=
        modelTorus m := by
  rw [model_normalizer_eq_borel,opposite_normalizer,modelBorel_inf_opposite_borel]

theorem map_torus_of_fix_opposite_pair (m : ℕ) (f : MulAut (ActualGroup m))
    (hU : (modelUnipotent m).map f.toMonoidHom=modelUnipotent m)
    (hO : (modelOppositeUnipotent m).map f.toMonoidHom=modelOppositeUnipotent m) :
    (modelTorus m).map f.toMonoidHom=modelTorus m := by
  rw [←pair_normalizer_eq_torus,Subgroup.map_inf _ _ _ f.injective,
    Subgroup.map_normalizer_eq_of_bijective _ f.bijective,
    Subgroup.map_normalizer_eq_of_bijective _ f.bijective,hU,hO]

/-- The Weyl displacement of an automorphism preserving the original
opposite pair lies in the actual pair normalizer, hence in the actual
diagonal torus. -/
theorem weyl_displacement_mem_torus (m : ℕ) (f : MulAut (ActualGroup m))
    (hU : (modelUnipotent m).map f.toMonoidHom=modelUnipotent m)
    (hO : (modelOppositeUnipotent m).map f.toMonoidHom=modelOppositeUnipotent m) :
    f (modelWeyl m)*(modelWeyl m)⁻¹∈modelTorus m := by
  let P := originalSylow m
  let w := modelWeyl m
  have hfP : f • P=P := Sylow.ext hU
  have hfO : f • (w • P)=w • P := Sylow.ext hO
  have hw : w⁻¹=w := Subtype.ext (CFSGSuzukiTorus.weylElement_inv m)
  have hfw : (f w)⁻¹=f w := by rw [←map_inv,hw]
  have hcomm : f*MulAut.conj w=MulAut.conj (f w)*f := by
    apply MulEquiv.ext
    intro x
    change f (w*x*w⁻¹)=f w*f x*(f w)⁻¹
    simp only [map_mul,map_inv]
  have hs : (f w) • P=w • P := by
    calc
      (f w) • P=(MulAut.conj (f w)) • (f • P) := by rw [hfP]; rfl
      _ = (f*MulAut.conj w) • P := by rw [hcomm,mul_smul]
      _ = f • (w • P) := mul_smul f (MulAut.conj w) P
      _ = w • P := hfO
  have hback : (f w) • (w • P)=P := by
    have hh := inv_smul_smul (f w) P
    rw [hfw,hs] at hh
    exact hh
  have htP : (f w*w⁻¹) • P=P := by rw [mul_smul,hw,hback]
  have htO : (f w*w⁻¹) • (w • P)=w • P := by
    rw [mul_smul,inv_smul_smul,hs]
  rw [←pair_normalizer_eq_torus]
  exact ⟨Sylow.smul_eq_iff_mem_normalizer.mp htP,
    Sylow.smul_eq_iff_mem_normalizer.mp htO⟩

theorem exists_inner_preserve_U_opposite_torus (m : ℕ) (f : MulAut (ActualGroup m)) :
    ∃ g : ActualGroup m,
      (modelUnipotent m).map (MulAut.conj g*f).toMonoidHom=modelUnipotent m ∧
      (modelOppositeUnipotent m).map (MulAut.conj g*f).toMonoidHom=
        modelOppositeUnipotent m ∧
      (modelTorus m).map (MulAut.conj g*f).toMonoidHom=modelTorus m := by
  obtain ⟨g,hU,hO⟩ := exists_inner_fix_opposite_pair m f
  have hU' : (modelUnipotent m).map (MulAut.conj g*f).toMonoidHom=modelUnipotent m := by
    have hh := congrArg (fun P : Sylow 2 (ActualGroup m) => P.toSubgroup) hU
    exact hh
  have hO' : (modelOppositeUnipotent m).map (MulAut.conj g*f).toMonoidHom=
      modelOppositeUnipotent m := by
    have hh := congrArg (fun P : Sylow 2 (ActualGroup m) => P.toSubgroup) hO
    exact hh
  exact ⟨g,hU',hO',map_torus_of_fix_opposite_pair m _ hU' hO'⟩

end SymmetricSubgroupAsymptotics.CFSGSuzukiAlignedAutomorphisms
