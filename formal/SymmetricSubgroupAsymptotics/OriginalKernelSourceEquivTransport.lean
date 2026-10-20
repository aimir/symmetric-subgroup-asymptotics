import SymmetricSubgroupAsymptotics.Non2LiftBound

/-! Transport an actual elementary-kernel chart along a source group
isomorphism. The target module and its action are unchanged. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
variable {G H B : Type} [Group G] [Group H] [Group B]
  (pi : H →* B) (A : Rep.{0} (ZMod 2) B)
  (E : OriginalKernelModuleChart pi A) (e : G ≃* H)

private def sourceKernelEquiv : pi.ker ≃* (pi.comp e.toMonoidHom).ker where
  toFun h := ⟨e.symm h.val,by
    change pi (e (e.symm h.val))=1
    rw [e.apply_symm_apply]
    exact h.property⟩
  invFun g := ⟨e g.val,g.property⟩
  left_inv h := Subtype.ext (e.apply_symm_apply h.val)
  right_inv g := Subtype.ext (e.symm_apply_apply g.val)
  map_mul' h k := Subtype.ext (e.symm.map_mul h.val k.val)

/-- This retains the exact conjugation action of the original source. -/
def ofSourceEquiv : OriginalKernelModuleChart (pi.comp e.toMonoidHom) A where
  equiv := E.equiv.trans (sourceKernelEquiv pi e)
  conjugate g a := by
    apply e.injective
    change e (e.symm (E.equiv (Multiplicative.ofAdd (A.ρ (pi (e g)) a)) : H))=
      e (g * e.symm (E.equiv (Multiplicative.ofAdd a) : H) * g⁻¹)
    rw [e.apply_symm_apply,map_mul,map_mul,map_inv,e.apply_symm_apply]
    exact E.conjugate (e g) a

end SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
