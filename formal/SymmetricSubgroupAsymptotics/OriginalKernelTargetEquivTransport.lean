import SymmetricSubgroupAsymptotics.Non2LiftBound

/-! Change only the literal model of an original quotient. The source
and its full correlated kernel are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
variable {k G B C : Type} [CommRing k] [Group G] [Group B] [Group C]
    (pi : G →* B) (A : Rep k B) (E : OriginalKernelModuleChart pi A) (e : B ≃* C)

def targetRep : Rep k C := Rep.of (A.ρ.comp e.symm.toMonoidHom)

def ofTargetEquiv : OriginalKernelModuleChart (e.toMonoidHom.comp pi) (targetRep A e) where
  equiv := E.equiv.trans (MulEquiv.subgroupCongr (by
    ext g
    change pi g=1 ↔ e (pi g)=1
    constructor
    · intro h
      rw [h,map_one]
    · intro h
      apply e.injective
      simpa only [map_one] using h))
  conjugate g v := by
    change (E.equiv (Multiplicative.ofAdd (A.ρ (e.symm (e (pi g))) v)) : G)=_
    rw [e.symm_apply_apply]
    exact E.conjugate g v

end SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
