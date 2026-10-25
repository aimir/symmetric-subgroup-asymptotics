import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.SetTheory.Cardinal.Finite

/-! Burnside counting for an actual surjection whose fibres are exactly
the orbits of the displayed group action. The target is identified with
that actual orbit quotient, rather than substituted by its cardinal. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics.FiniteActionFibreBurnside
variable {P X Y : Type*} [Group P] [MulAction P X]

def orbitQuotientEquiv (f : X → Y) (hf : Function.Surjective f)
    (hmap : ∀ (g : P) (x : X), f (g • x)=f x)
    (hfibre : ∀ x y : X, f x=f y → ∃ g : P, g • y=x) :
    MulAction.orbitRel.Quotient P X ≃ Y := by
  let q : MulAction.orbitRel.Quotient P X → Y := Quotient.lift f (by
    intro x y hxy
    obtain ⟨g,hg⟩ := hxy
    rw [←hg]
    exact hmap g y)
  apply Equiv.ofBijective q
  constructor
  · intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro x y hxy
    exact Quotient.sound (hfibre x y hxy)
  · intro y
    obtain ⟨x,rfl⟩ := hf y
    exact ⟨Quotient.mk _ x,rfl⟩

theorem card_mul_group_eq_sum_fixed [Finite P] [Finite X] [Finite Y]
    (f : X → Y) (hf : Function.Surjective f)
    (hmap : ∀ (g : P) (x : X), f (g • x)=f x)
    (hfibre : ∀ x y : X, f x=f y → ∃ g : P, g • y=x) :
    Nat.card Y*Nat.card P=∑ g : P, Nat.card (MulAction.fixedBy X g) := by
  classical
  letI : Fintype P := Fintype.ofFinite P
  letI : Fintype X := Fintype.ofFinite X
  letI : Fintype (MulAction.orbitRel.Quotient P X) := Fintype.ofFinite _
  letI (g : P) : Fintype (MulAction.fixedBy X g) := Fintype.ofFinite _
  have hcard := Nat.card_congr (orbitQuotientEquiv f hf hmap hfibre)
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group P X
  simpa only [←Nat.card_eq_fintype_card,hcard] using hburn.symm

end SymmetricSubgroupAsymptotics.FiniteActionFibreBurnside
