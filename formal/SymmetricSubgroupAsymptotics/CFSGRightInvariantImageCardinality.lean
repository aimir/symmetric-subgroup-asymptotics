import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Subgroup.Basic

/-! Charge the literal size of a right-invariant fibre to the image.
No normality or freeness assumption on the subgroup is needed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGRightInvariantImageCardinality
variable {G X : Type*} [Group G] [Finite G]

theorem image_card_mul_subgroup_le (f : G→X) (C : Subgroup G)
    (hC : ∀g : G,∀c : C,f (g*c)=f g) :
    Nat.card (Set.range f)*Nat.card C≤Nat.card G := by
  classical
  let rep : Set.range f→G := fun x=>Classical.choose x.property
  have hrep (x : Set.range f) : f (rep x)=x.val := Classical.choose_spec x.property
  let enc : Set.range f×C→G := fun x=>rep x.1*x.2
  have hinj : Function.Injective enc := by
    rintro ⟨x,c⟩ ⟨y,d⟩ he
    have hxy : x=y := by
      apply Subtype.ext
      have hh := congrArg f he
      change f (rep x*c)=f (rep y*d) at hh
      rw [hC,hC,hrep,hrep] at hh
      exact hh
    subst y
    have hcd : c=d := by
      apply Subtype.ext
      exact mul_left_cancel he
    exact Prod.ext rfl hcd
  calc
    _=Nat.card (Set.range f×C) := (Nat.card_prod _ _).symm
    _≤Nat.card G := Nat.card_le_card_of_injective enc hinj

end SymmetricSubgroupAsymptotics.CFSGRightInvariantImageCardinality
