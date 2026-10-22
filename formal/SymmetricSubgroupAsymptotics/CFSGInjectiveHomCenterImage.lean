import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.Subgroup.Ker

/-! The actual centre of the range of an injective group homomorphism
is exactly the image of the actual source centre. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGInjectiveHomCenterImage
variable {G Q : Type*} [Group G] [Group Q]

theorem center_range_image_eq (f : G→*Q) (hf : Function.Injective f) :
    (Subgroup.center f.range).map f.range.subtype=(Subgroup.center G).map f := by
  let e : G≃*f.range := MonoidHom.ofInjective hf
  apply Subgroup.ext
  intro x
  constructor
  · rintro ⟨z,hzc,hzx⟩
    let y := e.symm z
    have hy : y∈Subgroup.center G := ((Subgroup.centerCongr e).symm ⟨z,hzc⟩).property
    refine ⟨y,hy,?_⟩
    have he := congrArg (fun z : f.range=>z.val) (e.apply_symm_apply z)
    change f y=z.val at he
    exact he.trans hzx
  · rintro ⟨z,hz,hzx⟩
    refine ⟨e z,(Subgroup.centerCongr e ⟨z,hz⟩).property,?_⟩
    change f z=x
    exact hzx

end SymmetricSubgroupAsymptotics.CFSGInjectiveHomCenterImage
