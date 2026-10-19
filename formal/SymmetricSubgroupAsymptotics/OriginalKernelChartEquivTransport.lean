import SymmetricSubgroupAsymptotics.Non2LiftBound

/-! Transport an original kernel chart along an actual group equivalence.
Only the source group changes; the acting image and module are literal. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
variable {p : ℕ} {G H B : Type} [Group G] [Group H] [Group B]
  (pi : H →* B) (A : Rep.{0} (ZMod p) B) (E : OriginalKernelModuleChart pi A)
  (e : G ≃* H)

def equivKernel : pi.ker ≃* (pi.comp e.toMonoidHom).ker where
  toFun x := ⟨e.symm x,by change pi (e (e.symm x))=1; rw [e.apply_symm_apply]; exact x.property⟩
  invFun x := ⟨e x,x.property⟩
  left_inv x := Subtype.ext (e.apply_symm_apply x)
  right_inv x := Subtype.ext (e.symm_apply_apply x)
  map_mul' x y := Subtype.ext (e.symm.map_mul x y)

include E in
def ofSourceEquiv : OriginalKernelModuleChart (pi.comp e.toMonoidHom) A where
  equiv := E.equiv.trans (equivKernel pi e)
  conjugate g a := by
    have h := congrArg e.symm (E.conjugate (e g) a)
    change e.symm (E.equiv (Multiplicative.ofAdd (A.ρ (pi (e g)) a)) : H)=
      g*e.symm (E.equiv (Multiplicative.ofAdd a) : H)*g⁻¹
    simpa only [map_mul,map_inv,MulEquiv.symm_apply_apply] using h

end SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
