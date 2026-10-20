import SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequencesWeighted

/-! Reassociate actual orbit families into the weighted list theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequences
open MarkedC4
namespace ActionShape

variable {G : Type} [Group G]

theorem familyHom_profile (n : ℕ) (X : Fin n → Type)
    [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    (f : G →* ∀ i, Equiv.Perm (X i))
    (ht : ∀ i, letI : MulAction G (X i) :=
      MulAction.compHom (X i) ((Pi.evalMonoidHom _ i).comp f)
      MulAction.IsPretransitive G (X i)) :
    TransitiveProfile (familyHom n X f) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_, ?_⟩
    · exact ht 0
    · apply ih (fun i => X i.succ) ((finTail X).comp f)
      intro i
      exact ht i.succ

theorem weight_ofFamily (v : ℕ → ℝ) (n : ℕ) (X : Fin n → Type)
    [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)] :
    (ofFamily n X).weight v = ∑ i, v (Fintype.card (X i)) := by
  induction n with
  | zero => simp [ofFamily, weight]
  | succ n ih =>
    change v (Fintype.card (X 0)) +
      (ofFamily n (fun i => X i.succ)).weight v = _
    rw [ih]
    exact (Fin.sum_univ_succ
      (fun i : Fin (n + 1) => v (Fintype.card (X i)))).symm

end ActionShape

/-- The weighted bound for an arbitrary literal finite family of transitive
point actions, still retaining its original correlated source. -/
theorem family_generator_bound
    (hgen : PrimitiveNormalGeneratorInput)
    (hTracey : TraceyRefinedInducedModuleInput)
    (hcomp : PrimitiveCompositionLengthInput)
    (G : Type) [Group G] [Finite G] [IsSolvable G]
    (n : ℕ) (X : Fin n → Type)
    [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    (f : G →* ∀ i, Equiv.Perm (X i))
    (hf : Function.Injective f)
    (ht : ∀ i, letI : MulAction G (X i) :=
      MulAction.compHom (X i) ((Pi.evalMonoidHom _ i).comp f)
      MulAction.IsPretransitive G (X i)) :
    (genRank G : ℝ) ≤ 128 * ∑ i, orbitWeight (Fintype.card (X i)) := by
  have h := weighted_generator_bound hgen hTracey hcomp
    (ActionShape.ofFamily n X) G (ActionShape.familyHom n X f)
    (ActionShape.familyHom_injective n X f hf)
    (ActionShape.familyHom_profile n X f ht)
  simpa only [ActionShape.weight_ofFamily] using h

end SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequences
