import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Concrete descent of a group homomorphism through a surjective
coordinate homomorphism whose kernel it kills, with exact intertwining. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSurjectiveGroupHomFactor
variable {G Q R : Type*} [Group G] [Group Q] [Group R]

def factorHom (pi : G→*Q) (hpi : Function.Surjective pi) (d : G→*R)
    (hk : pi.ker≤d.ker) : Q→*R :=
  (QuotientGroup.lift pi.ker d hk).comp
    (QuotientGroup.quotientKerEquivOfSurjective pi hpi).symm.toMonoidHom

theorem factorHom_apply (pi : G→*Q) (hpi : Function.Surjective pi) (d : G→*R)
    (hk : pi.ker≤d.ker) (g : G) : factorHom pi hpi d hk (pi g)=d g := by
  let e := QuotientGroup.quotientKerEquivOfSurjective pi hpi
  have he : e (QuotientGroup.mk g)=pi g := rfl
  change QuotientGroup.lift pi.ker d hk (e.symm (pi g))=d g
  rw [←he,MulEquiv.symm_apply_apply]
  rfl

end SymmetricSubgroupAsymptotics.CFSGSurjectiveGroupHomFactor
