import SymmetricSubgroupAsymptotics.CFSGSolubleOrbitWeighted
import SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequencesFamilies

/-! The original correlated finite orbit family, with no sharp primitive input. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSolubleOrbitConsequences
open MarkedC4 LargeOrbitGeneratorConsequences

/-- The weighted bound for an arbitrary literal finite family of transitive
point actions, still retaining its original correlated source. -/
theorem family_generator_bound
    (hTracey : TraceyRefinedInducedModuleInput)
    (G : Type) [Group G] [Finite G] [IsSolvable G]
    (n : ℕ) (X : Fin n → Type)
    [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    (f : G →* ∀ i, Equiv.Perm (X i))
    (hf : Function.Injective f)
    (ht : ∀ i, letI : MulAction G (X i) :=
      MulAction.compHom (X i) ((Pi.evalMonoidHom _ i).comp f)
      MulAction.IsPretransitive G (X i)) :
    (genRank G : ℝ) ≤ 1280 * ∑ i, orbitWeight (Fintype.card (X i)) := by
  have h := weighted_generator_bound hTracey
    (ActionShape.ofFamily n X) G (ActionShape.familyHom n X f)
    (ActionShape.familyHom_injective n X f hf)
    (ActionShape.familyHom_profile n X f ht)
  simpa only [ActionShape.weight_ofFamily] using h

end SymmetricSubgroupAsymptotics.CFSGSolubleOrbitConsequences
