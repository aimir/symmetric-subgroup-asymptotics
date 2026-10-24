import Mathlib.Algebra.Group.Subgroup.Basic

/-! Transport subgroup membership across an equality of labels while
keeping the ambient group element fixed. No dependent group subtype is
transported. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGGroupLabelSubgroupTransport

theorem twisted_product_mem_of_label_eq {G R : Type*} [Group G]
    (L : R → Subgroup G) (S : Subgroup G) (T : G → G)
    (r s : R) (hrs : r=s) (h : ∀ x ∈ L s, x*T x ∈ S)
    (x : G) (hx : x ∈ L r) : x*T x ∈ S := by
  apply h x
  exact hrs ▸ hx

end SymmetricSubgroupAsymptotics.CFSGGroupLabelSubgroupTransport
