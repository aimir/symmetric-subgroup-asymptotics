import SymmetricSubgroupAsymptotics.CFSGPSLTwoPairRestriction

/-! The original projective torus acts faithfully by inner automorphisms
and preserves the same opposite pair. Equality of its root scalars is
charged only modulo its actual square-one projective kernel. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoPairRestriction
open CFSGPSLTwoRootCoordinates CFSGPSLTwoGeometry
variable {F : Type*} [Field F] [Finite F]

theorem inner_pairTorus_injective :
    Function.Injective (fun t : pairTorus (F:=F) => MulAut.conj (t : PSL (F:=F))) := by
  intro t u he
  obtain ⟨c,hc⟩ := t.property
  obtain ⟨d,hd⟩ := u.property
  have hconj : MulAut.conj (projectiveTorus c)=MulAut.conj (projectiveTorus d) := by
    change MulAut.conj (projectiveTorusHom c)=MulAut.conj (projectiveTorusHom d)
    rw [hc,hd]
    exact he
  have hu := congrArg (fun A : MulAut (PSL (F:=F)) => A (projectiveUpper 1)) hconj
  change projectiveTorus c*projectiveUpper 1*(projectiveTorus c)⁻¹=
    projectiveTorus d*projectiveUpper 1*(projectiveTorus d)⁻¹ at hu
  rw [projective_torus_conjugation,projective_torus_conjugation,mul_one,mul_one] at hu
  have hs : (c : F)^2=(d : F)^2 := projectiveUpper_injective hu
  have hcd : (((c*d⁻¹ : Fˣ) : F))^2=1 := by
    simp only [Units.val_mul,Units.val_inv_eq_inv_val,mul_pow,inv_pow,hs,
      mul_inv_cancel₀ (pow_ne_zero 2 (Units.ne_zero d))]
  have ht := projectiveTorus_eq_one_of_square (c*d⁻¹) hcd
  change projectiveTorusHom (c*d⁻¹)=1 at ht
  rw [map_mul,map_inv] at ht
  have hpar : projectiveTorusHom c=projectiveTorusHom d := mul_inv_eq_one.mp ht
  apply Subtype.ext
  exact hc.symm.trans (hpar.trans hd)

theorem pairTorus_conj_mem_pair (t : pairTorus (F:=F)) :
    MulAut.conj (t : PSL (F:=F))∈pairStabilizer (F:=F) := by
  have ht := (pair_normalizer_eq_torus (F:=F)).ge t.property
  constructor
  · exact SetLike.coe_injective (Subgroup.mem_normalizer_iff_conj_image_eq.mp ht.1)
  · exact SetLike.coe_injective (Subgroup.mem_normalizer_iff_conj_image_eq.mp ht.2)

end SymmetricSubgroupAsymptotics.CFSGPSLTwoPairRestriction
