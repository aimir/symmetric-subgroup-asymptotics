import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.Action.End

/-! Actual automorphisms on an additive quotient whose kernel is the
intrinsic centre. The map intertwines the original quotient homomorphism;
no chosen coordinates or automorphism-classification premise is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGCentralQuotientAutomorphism
variable {G V : Type*} [Group G] [AddCommGroup V]
variable (pi : G →* Multiplicative V) (hpi : Function.Surjective pi)
variable (hker : pi.ker = Subgroup.center G)

include hker in
theorem kernel_map_aut (f : MulAut G) : pi.ker.map f.toMonoidHom = pi.ker := by
  rw [hker]
  exact Subgroup.characteristic_iff_map_eq.mp inferInstance f

def quotientEquiv : G ⧸ pi.ker ≃* Multiplicative V :=
  QuotientGroup.quotientKerEquivOfSurjective pi hpi

theorem quotientEquiv_mk (g : G) :
    quotientEquiv pi hpi (QuotientGroup.mk' pi.ker g) = pi g := rfl

def quotientMulAut (f : MulAut G) : MulAut (Multiplicative V) :=
  (quotientEquiv pi hpi).symm.trans
    ((QuotientGroup.congr pi.ker pi.ker f (kernel_map_aut pi hker f)).trans
      (quotientEquiv pi hpi))

theorem quotientMulAut_first (f : MulAut G) (g : G) :
    quotientMulAut pi hpi hker f (pi g) = pi (f g) := by
  change quotientEquiv pi hpi (QuotientGroup.congr pi.ker pi.ker f
    (kernel_map_aut pi hker f) ((quotientEquiv pi hpi).symm (pi g))) = _
  rw [← quotientEquiv_mk pi hpi g, MulEquiv.symm_apply_apply,
    QuotientGroup.congr_mk', quotientEquiv_mk]

def quotientAddAut (f : MulAut G) : AddAut V where
  toFun v := (quotientMulAut pi hpi hker f (Multiplicative.ofAdd v)).toAdd
  invFun v := ((quotientMulAut pi hpi hker f).symm (Multiplicative.ofAdd v)).toAdd
  left_inv v := (quotientMulAut pi hpi hker f).symm_apply_apply (Multiplicative.ofAdd v)
  right_inv v := (quotientMulAut pi hpi hker f).apply_symm_apply (Multiplicative.ofAdd v)
  map_add' v w := map_mul (quotientMulAut pi hpi hker f)
    (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)

theorem quotientAddAut_first (f : MulAut G) (g : G) :
    quotientAddAut pi hpi hker f (pi g).toAdd = (pi (f g)).toAdd :=
  congrArg Multiplicative.toAdd (quotientMulAut_first pi hpi hker f g)

def quotientAddAutHom : MulAut G →* AddAut V where
  toFun := quotientAddAut pi hpi hker
  map_one' := by
    apply AddEquiv.ext
    intro v
    obtain ⟨g, hg⟩ := hpi (Multiplicative.ofAdd v)
    have hv : (pi g).toAdd = v := congrArg Multiplicative.toAdd hg
    have he := quotientAddAut_first pi hpi hker 1 g
    change quotientAddAut pi hpi hker 1 (pi g).toAdd = (pi g).toAdd at he
    change quotientAddAut pi hpi hker 1 v = v
    simpa only [hv] using he
  map_mul' a b := by
    apply AddEquiv.ext
    intro v
    obtain ⟨g, hg⟩ := hpi (Multiplicative.ofAdd v)
    have hv : (pi g).toAdd = v := congrArg Multiplicative.toAdd hg
    change quotientAddAut pi hpi hker (a * b) v =
      quotientAddAut pi hpi hker a (quotientAddAut pi hpi hker b v)
    rw [← hv, quotientAddAut_first, quotientAddAut_first, quotientAddAut_first]
    rfl

end SymmetricSubgroupAsymptotics.CFSGCentralQuotientAutomorphism
