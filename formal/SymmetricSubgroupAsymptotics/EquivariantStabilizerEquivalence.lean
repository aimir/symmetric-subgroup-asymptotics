import Mathlib.GroupTheory.GroupAction.Basic

/-! Equivariant actual group and carrier coordinates identify the
actual point stabilizers. This retains the chosen point and the SAME
action, rather than replacing a stabilizer by an unrelated subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.EquivariantStabilizerEquivalence
variable {G H X Y : Type*} [Group G] [Group H] [MulAction G X] [MulAction H Y]

def stabilizerEquiv (e : G ≃* H) (E : X ≃ Y)
    (hE : ∀ g x, E (g • x) = e g • E x) (x : X) :
    MulAction.stabilizer G x ≃* MulAction.stabilizer H (E x) where
  toFun g := ⟨e g.val, by
    change e g.val • E x = E x
    have hg : g.val • x = x := g.property
    exact (hE g.val x).symm.trans (congrArg E hg)⟩
  invFun g := ⟨e.symm g.val, by
    change e.symm g.val • x = x
    apply E.injective
    rw [hE, e.apply_symm_apply]
    exact g.property⟩
  left_inv g := Subtype.ext (e.symm_apply_apply g.val)
  right_inv g := Subtype.ext (e.apply_symm_apply g.val)
  map_mul' g h := Subtype.ext (e.map_mul g.val h.val)

theorem stabilizerEquiv_apply (e : G ≃* H) (E : X ≃ Y)
    (hE : ∀ g x, E (g • x) = e g • E x) (x : X)
    (g : MulAction.stabilizer G x) :
    (stabilizerEquiv e E hE x g).val = e g.val := rfl

end SymmetricSubgroupAsymptotics.EquivariantStabilizerEquivalence
