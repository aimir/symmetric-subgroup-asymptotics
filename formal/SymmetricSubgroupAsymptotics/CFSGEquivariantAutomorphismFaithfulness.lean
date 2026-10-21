import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Equiv.Basic

/-! A faithful action of a group detects automorphisms acting compatibly
on the same literal objects. This is useful for conjugacy-stable root
families: no additional faithfulness assumption for their automorphism
action is needed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGEquivariantAutomorphismFaithfulness
variable {G A X : Type*} [Group G] [Group A]
  [MulAction G X] [FaithfulSMul G X] [MulAction A X]

theorem automorphism_eq_one_of_trivial_action (phi : A →* MulAut G)
    (hcompat : ∀ a : A, ∀ g : G, ∀ x : X,
      a • (g • x) = (phi a g) • (a • x))
    (a : A) (ha : ∀ x : X, a • x = x) : phi a = 1 := by
  ext g
  apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
  intro x
  have hx := hcompat a g x
  rw [ha, ha] at hx
  exact hx.symm

theorem faithfulSMul_of_injective (phi : A →* MulAut G)
    (hphi : Function.Injective phi)
    (hcompat : ∀ a : A, ∀ g : G, ∀ x : X,
      a • (g • x) = (phi a g) • (a • x)) : FaithfulSMul A X := by
  constructor
  intro a b hab
  have htriv : ∀ x : X, (a⁻¹ * b) • x = x := by
    intro x
    rw [mul_smul, ← hab x, inv_smul_smul]
  have heq := automorphism_eq_one_of_trivial_action phi hcompat (a⁻¹ * b) htriv
  apply hphi
  apply inv_mul_eq_one.mp
  simpa only [map_mul, map_inv] using heq

theorem faithfulSMul_automorphisms [MulAction (MulAut G) X]
    (hcompat : ∀ a : MulAut G, ∀ g : G, ∀ x : X,
      a • (g • x) = (a g) • (a • x)) : FaithfulSMul (MulAut G) X :=
  faithfulSMul_of_injective (MonoidHom.id (MulAut G)) Function.injective_id hcompat

end SymmetricSubgroupAsymptotics.CFSGEquivariantAutomorphismFaithfulness
