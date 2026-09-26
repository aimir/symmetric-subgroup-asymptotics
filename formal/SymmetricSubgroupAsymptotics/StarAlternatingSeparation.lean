import SymmetricSubgroupAsymptotics.StarAlternatingHead

/-! The whole star family separates the original coordinate space when
its horizontal space is nontrivial. Pulling that family back through an
original evaluation map therefore proves the map injective; no basis or
quotient-dimension assumption is required in advance. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {k U : Type*} [Field k] [AddCommGroup U] [Module k U] [Nontrivial U]

/-- All star parameters together have zero common radical. -/
theorem starAlternatingFamily_separates (x : U × k)
    (hx : ∀ l : Module.Dual k U, ∀ y, starAlternatingFamily l x y = 0) : x = 0 := by
  have hu : x.1 = 0 := by
    apply (Module.forall_dual_apply_eq_zero_iff k x.1).mp
    intro l
    simpa only [starAlternatingFamily_apply, map_zero, mul_one, mul_zero, sub_zero]
      using hx l (0, 1)
  obtain ⟨u, hu0⟩ := exists_ne (0 : U)
  obtain ⟨l, hlu⟩ := Module.Projective.exists_dual_ne_zero k hu0
  have ht : x.2 = 0 := by
    have hm : x.2 * l u = 0 := by
      simpa only [starAlternatingFamily_apply, mul_zero, zero_sub, neg_eq_zero]
        using hx l (u, 0)
    exact (mul_eq_zero.mp hm).resolve_right hlu
  exact Prod.ext hu ht

variable {E V L : Type*} [AddCommGroup E] [Module k E]
    [AddCommGroup V] [Module k V] [AddCommGroup L] [Module k L]

/-- The original map is injective whenever its actual pulled-back forms
are the complete star family in genuine parameter/input coordinates.
Surjectivity of the original map is not needed for this implication. -/
theorem linearMap_injective_of_pullback_star
    (f : E →ₗ[k] V) (eE : E ≃ₗ[k] U × k)
    (eL : L ≃ₗ[k] Module.Dual k U)
    (F : L →ₗ[k] (V →ₗ[k] V →ₗ[k] k))
    (hF : ∀ l x y, F l (f x) (f y) =
      starAlternatingFamily (eL l) (eE x) (eE y)) :
    Function.Injective f := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  apply eE.injective
  rw [map_zero]
  apply starAlternatingFamily_separates
  intro l y
  obtain ⟨l, rfl⟩ := eL.surjective l
  obtain ⟨y, rfl⟩ := eE.surjective y
  have hz : F l (f x) (f y) = 0 := by
    rw [show f x = 0 from hx, map_zero, LinearMap.zero_apply]
  exact (hF l x y).symm.trans hz

end SymmetricSubgroupAsymptotics
