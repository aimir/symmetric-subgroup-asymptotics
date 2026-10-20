import SymmetricSubgroupAsymptotics.SemisimpleExtensionProductSubquotient
import SymmetricSubgroupAsymptotics.ModuleSubquotientGeneratorBound

/-! The actual kernel and top sources occupy disjoint positions in one
common envelope. Its generator slots control the entire semisimple target. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

theorem semisimple_extension_generated_of_common_envelope
    {R A E M : Type} [Ring R]
    [AddCommGroup A] [Module R A] [IsSemisimpleModule R A]
    [AddCommGroup E] [Module R E]
    [AddCommGroup M] [Module R M]
    (K : Submodule R A)
    (q : E →ₗ[R] K) (hq : Function.Surjective q)
    (i : E →ₗ[R] M) (hi : Function.Injective i)
    (j : (A ⧸ K) →ₗ[R] M) (hj : Function.Injective j)
    (hdisjoint : Disjoint i.range j.range)
    (n : ℕ) (huniform : ∀ U : Submodule R M, ModuleGeneratedBy R U n) :
    ModuleGeneratedBy R A n := by
  obtain ⟨_, g, _, hg⟩ := semisimple_extension_product_subquotient K q hq i hi j hj
  have hsum : Function.Injective (i.coprod j) := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_coprod_of_disjoint_range i j hdisjoint,
      LinearMap.ker_eq_bot.mpr hi, LinearMap.ker_eq_bot.mpr hj]
    simp
  exact ModuleGeneratedBy.of_subquotient n huniform (i.coprod j) hsum g hg

end SymmetricSubgroupAsymptotics

end
