import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Action.End

/-! An actual automorphism action preserving the kernel of a surjective
additive quotient acts on that quotient. The kernel need not be
characteristic under automorphisms outside the given action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGInvariantQuotientAutomorphism
variable {A G V : Type*} [Group A] [Group G] [AddCommGroup V]
variable (pi : G →* Multiplicative V) (hpi : Function.Surjective pi)
variable (rho : A →* MulAut G) (hker : ∀ a : A,pi.ker.map (rho a).toMonoidHom=pi.ker)

def quotientEquiv : G ⧸ pi.ker ≃* Multiplicative V :=
  QuotientGroup.quotientKerEquivOfSurjective pi hpi

theorem quotientEquiv_mk (g : G) :
    quotientEquiv pi hpi (QuotientGroup.mk' pi.ker g)=pi g := rfl

def quotientMulAut (a : A) : MulAut (Multiplicative V) :=
  (quotientEquiv pi hpi).symm.trans
    ((QuotientGroup.congr pi.ker pi.ker (rho a) (hker a)).trans (quotientEquiv pi hpi))

theorem quotientMulAut_first (a : A) (g : G) :
    quotientMulAut pi hpi rho hker a (pi g)=pi (rho a g) := by
  change quotientEquiv pi hpi (QuotientGroup.congr pi.ker pi.ker (rho a)
    (hker a) ((quotientEquiv pi hpi).symm (pi g)))=_
  rw [←quotientEquiv_mk pi hpi g,MulEquiv.symm_apply_apply,
    QuotientGroup.congr_mk',quotientEquiv_mk]

def quotientAddAut (a : A) : AddAut V where
  toFun v := (quotientMulAut pi hpi rho hker a (Multiplicative.ofAdd v)).toAdd
  invFun v := ((quotientMulAut pi hpi rho hker a).symm (Multiplicative.ofAdd v)).toAdd
  left_inv v := (quotientMulAut pi hpi rho hker a).symm_apply_apply (Multiplicative.ofAdd v)
  right_inv v := (quotientMulAut pi hpi rho hker a).apply_symm_apply (Multiplicative.ofAdd v)
  map_add' v w := map_mul (quotientMulAut pi hpi rho hker a)
    (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)

theorem quotientAddAut_first (a : A) (g : G) :
    quotientAddAut pi hpi rho hker a (pi g).toAdd=(pi (rho a g)).toAdd :=
  congrArg (fun z : Multiplicative V => z.toAdd) (quotientMulAut_first pi hpi rho hker a g)

def quotientAddAutHom : A →* AddAut V where
  toFun := quotientAddAut pi hpi rho hker
  map_one' := by
    apply AddEquiv.ext
    intro v
    obtain ⟨g,hg⟩ := hpi (Multiplicative.ofAdd v)
    have hv : (pi g).toAdd=v := congrArg (fun z : Multiplicative V => z.toAdd) hg
    change quotientAddAut pi hpi rho hker 1 v=v
    rw [←hv,quotientAddAut_first]
    rw [map_one]
    rfl
  map_mul' a b := by
    apply AddEquiv.ext
    intro v
    obtain ⟨g,hg⟩ := hpi (Multiplicative.ofAdd v)
    have hv : (pi g).toAdd=v := congrArg (fun z : Multiplicative V => z.toAdd) hg
    change quotientAddAut pi hpi rho hker (a*b) v=
      quotientAddAut pi hpi rho hker a (quotientAddAut pi hpi rho hker b v)
    rw [←hv,quotientAddAut_first,quotientAddAut_first,quotientAddAut_first,map_mul]
    rfl

end SymmetricSubgroupAsymptotics.CFSGInvariantQuotientAutomorphism
