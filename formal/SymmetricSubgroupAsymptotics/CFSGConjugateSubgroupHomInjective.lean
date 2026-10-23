import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! Injectivity of a genuine group homomorphism on a subgroup transfers
to its actual conjugate. No assertion about the full homomorphism kernel
is needed, so this applies to the checked positive/opposite projective
charts even when global source faithfulness has not been proved. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupHomInjective

theorem injective_on_conjugate {G Q : Type*} [Group G] [Group Q]
    (f : G→*Q) (U V : Subgroup G) (g : G)
    (hV : U.map (MulAut.conj g).toMonoidHom=V)
    (hinj : Function.Injective (f.comp U.subtype)) :
    Function.Injective (f.comp V.subtype) := by
  intro x y he
  change f x.val=f y.val at he
  have hx : x.val∈U.map (MulAut.conj g).toMonoidHom := by rw [hV];exact x.property
  have hy : y.val∈U.map (MulAut.conj g).toMonoidHom := by rw [hV];exact y.property
  obtain ⟨u,hu,hux⟩ := hx
  obtain ⟨v,hv,hvy⟩ := hy
  have hc : f g*f u*(f g)⁻¹=f g*f v*(f g)⁻¹ := by
    have hh := (congrArg f hux).trans (he.trans (congrArg f hvy).symm)
    change f (g*u*g⁻¹)=f (g*v*g⁻¹) at hh
    simpa only [map_mul,map_inv] using hh
  have hfu : f u=f v := mul_left_cancel (mul_right_cancel hc)
  have huv : u=v := congrArg (fun z : U=>z.val)
    (hinj (show (f.comp U.subtype) ⟨u,hu⟩=(f.comp U.subtype) ⟨v,hv⟩ from hfu))
  apply Subtype.ext
  exact hux.symm.trans ((congrArg (MulAut.conj g) huv).trans hvy)

end SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupHomInjective
