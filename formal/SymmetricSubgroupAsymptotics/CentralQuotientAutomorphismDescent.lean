import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.Action.End

/-! Automorphisms descend to an actual group-valued quotient whose kernel
is the FULL intrinsic centre. The quotient target need not be abelian.
This is descent of existing source automorphisms, not an assertion that
arbitrary target automorphisms lift. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CentralQuotientAutomorphismDescent
variable {G H : Type*} [Group G] [Group H]
variable (pi : G →* H) (hpi : Function.Surjective pi)
variable (hker : pi.ker = Subgroup.center G)

include hker in
theorem kernel_map_aut (f : MulAut G) : pi.ker.map f.toMonoidHom = pi.ker := by
  rw [hker]
  exact Subgroup.characteristic_iff_map_eq.mp inferInstance f

def quotientEquiv : G ⧸ pi.ker ≃* H :=
  QuotientGroup.quotientKerEquivOfSurjective pi hpi

theorem quotientEquiv_mk (g : G) :
    quotientEquiv pi hpi (QuotientGroup.mk' pi.ker g) = pi g := rfl

def quotientMulAut (f : MulAut G) : MulAut H :=
  (quotientEquiv pi hpi).symm.trans
    ((QuotientGroup.congr pi.ker pi.ker f (kernel_map_aut pi hker f)).trans
      (quotientEquiv pi hpi))

theorem quotientMulAut_first (f : MulAut G) (g : G) :
    quotientMulAut pi hpi hker f (pi g) = pi (f g) := by
  change quotientEquiv pi hpi (QuotientGroup.congr pi.ker pi.ker f
    (kernel_map_aut pi hker f) ((quotientEquiv pi hpi).symm (pi g))) = _
  rw [← quotientEquiv_mk pi hpi g, MulEquiv.symm_apply_apply,
    QuotientGroup.congr_mk', quotientEquiv_mk]

def quotientMulAutHom : MulAut G →* MulAut H where
  toFun := quotientMulAut pi hpi hker
  map_one' := by
    apply MulEquiv.ext
    intro x
    obtain ⟨g, rfl⟩ := hpi x
    change quotientMulAut pi hpi hker 1 (pi g) = pi g
    exact quotientMulAut_first pi hpi hker 1 g
  map_mul' a b := by
    apply MulEquiv.ext
    intro x
    obtain ⟨g, rfl⟩ := hpi x
    change quotientMulAut pi hpi hker (a*b) (pi g) =
      quotientMulAut pi hpi hker a (quotientMulAut pi hpi hker b (pi g))
    rw [quotientMulAut_first, quotientMulAut_first, quotientMulAut_first]
    rfl

theorem quotientMulAutHom_apply (f : MulAut G) (g : G) :
    quotientMulAutHom pi hpi hker f (pi g) = pi (f g) :=
  quotientMulAut_first pi hpi hker f g

end SymmetricSubgroupAsymptotics.CentralQuotientAutomorphismDescent
