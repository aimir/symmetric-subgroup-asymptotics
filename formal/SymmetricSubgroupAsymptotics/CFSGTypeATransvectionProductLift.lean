import SymmetricSubgroupAsymptotics.CFSGTypeAProjectiveTransvectionGeometry

/-! A product of two projective transvections that is again a projective
transvection lifts to the exact original SL product in dimension at least
three. The two factors have a common nonzero fixed vector; a scalar times
a unipotent transvection can fix that vector only when the scalar is one.
No intersection of three hyperplanes is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeATransvectionProductLift
open Module LinearMap

section Scalar
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem scalar_transvection_fixed_nonzero (f : Dual F V) (v x : V) (hf : f v=0)
    (hx : x≠0) (r : F) (he : r • LinearMap.transvection f v x=x) : r=1 := by
  by_cases hfx : f x=0
  · simp only [LinearMap.transvection.apply,hfx,zero_smul,add_zero] at he
    exact smul_left_injective F hx (by simpa only [one_smul] using he)
  · have hh := congrArg f he
    simp only [LinearMap.transvection.apply,map_add,map_smul,hf,
      smul_zero,smul_eq_mul,mul_zero,add_zero] at hh
    have hz : (r-1)*f x=0 := by rw [sub_mul,one_mul,hh,sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hfx)
end Scalar

open Matrix CFSGTypeAProjectivePointRoots
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

theorem transvection_product_eq_of_projective_eq (hn : 3≤Fintype.card n)
    {f g h : Dual F (n→F)} {v w u : n→F}
    (hf : f v=0) (hg : g w=0) (hh : h u=0)
    (he : projection (transvectionSL hf)*projection (transvectionSL hg)=
      projection (transvectionSL hh)) :
    transvectionSL hf*transvectionSL hg=transvectionSL hh := by
  rw [←map_mul] at he
  obtain ⟨r,_hr,hmat⟩ := projection_eq_implies_scalar_mul _ _ he
  obtain ⟨x,hx,hfx,hgx⟩ := exists_nonzero_joint_kernel f g
    (by simpa only [Module.finrank_fintype_fun_eq_card] using hn)
  have hfix : (transvectionSL hf*transvectionSL hg).toLin' x=x := by
    rw [map_mul]
    change (transvectionSL hf).toLin' ((transvectionSL hg).toLin' x)=x
    simp only [transvectionSL_apply,hfx,hgx,zero_smul,add_zero]
  have hscalar : (transvectionSL hf*transvectionSL hg).toLin' x=
      r • (transvectionSL hh).toLin' x := by
    change Matrix.toLin' (transvectionSL hf*transvectionSL hg).val x=
      r • Matrix.toLin' (transvectionSL hh).val x
    rw [hmat,Matrix.toLin'_mul_apply,scalar_toLin'_apply]
  have hr : r=1 := scalar_transvection_fixed_nonzero h u x hh hx r (by
    simpa only [transvectionSL_apply,LinearMap.transvection.apply] using hscalar.symm.trans hfix)
  apply Subtype.ext
  rw [hmat,hr,map_one,one_mul]

end SymmetricSubgroupAsymptotics.CFSGTypeATransvectionProductLift
