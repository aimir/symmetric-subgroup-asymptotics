import SymmetricSubgroupAsymptotics.SchurIsotypicGenerators

/-! Uniform submodule generation bounds all literal subquotient targets. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.ModuleGeneratedBy

variable {R E M A : Type} [Ring R]
    [AddCommGroup E] [Module R E]
    [AddCommGroup M] [Module R M]
    [AddCommGroup A] [Module R A]

theorem of_subquotient (n : ℕ)
    (huniform : ∀ U : Submodule R M, ModuleGeneratedBy R U n)
    (i : E →ₗ[R] M) (hi : Function.Injective i)
    (q : E →ₗ[R] A) (hq : Function.Surjective q) :
    ModuleGeneratedBy R A n := by
  let f : E →ₗ[R] i.range := i.rangeRestrict
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      exact hi (congrArg Subtype.val h)
    · rintro ⟨y, x, rfl⟩
      exact ⟨x, rfl⟩
  let e : E ≃ₗ[R] i.range := LinearEquiv.ofBijective f hf
  obtain ⟨v, hv⟩ := congr e.symm (huniform i.range)
  refine ⟨fun j => q (v j), ?_⟩
  have hmap := congrArg (Submodule.map q) hv
  rw [Submodule.map_top, LinearMap.range_eq_top.mpr hq, Submodule.map_span] at hmap
  rw [← Set.range_comp] at hmap
  simpa only [Function.comp_apply] using hmap

end SymmetricSubgroupAsymptotics.ModuleGeneratedBy

end
