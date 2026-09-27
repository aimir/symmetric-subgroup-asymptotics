import SymmetricSubgroupAsymptotics.TransitiveBinaryGenerators
import SymmetricSubgroupAsymptotics.CocycleGeneratorBound

/-! Uniform cocycle and first-cohomology bounds on every original quotient
of a faithful transitive binary group. The actual source generators are
constructed internally and mapped through the supplied onto map. The
representation, its action and its cohomology quotient remain unchanged. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {X B R : Type} [Finite X] [Group B] [CommRing R]

/-- The image of the constructed original tuple generates this exact
quotient, including a nonsplit quotient and the trivial source. -/
theorem transitiveBinary_quotient_exists_generating_tuple
    (k : ℕ) (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hdegree : Nat.card X = 2^k) (π : U →* B) (hπ : Function.Surjective π) :
    ∃ g : Fin (binaryCumulativeWidth k) → B,
      Subgroup.closure (Set.range g) = ⊤ := by
  obtain ⟨g, hg⟩ := transitiveBinary_exists_generating_tuple k U hU hdegree
  refine ⟨fun i => π (g i), ?_⟩
  have h := congrArg (Subgroup.map π) hg
  simpa only [MonoidHom.map_closure, ← Set.range_comp',
    Subgroup.map_top_of_surjective π hπ, Function.comp_def] using h

theorem transitiveBinary_quotient_cocycles_card_le
    (k : ℕ) (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hdegree : Nat.card X = 2^k) (π : U →* B) (hπ : Function.Surjective π)
    (A : Rep R B) [Finite A] :
    Nat.card (groupCohomology.cocycles₁ A) ≤
      Nat.card A ^ binaryCumulativeWidth k := by
  obtain ⟨g, hg⟩ := transitiveBinary_quotient_exists_generating_tuple k U hU hdegree π hπ
  exact cocycles_card_le_generator_power A (binaryCumulativeWidth k) g hg

theorem transitiveBinary_quotient_firstCohomology_card_le
    (k : ℕ) (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hdegree : Nat.card X = 2^k) (π : U →* B) (hπ : Function.Surjective π)
    (A : Rep R B) [Finite A] :
    Nat.card (groupCohomology.H1 A) ≤ Nat.card A ^ binaryCumulativeWidth k := by
  obtain ⟨g, hg⟩ := transitiveBinary_quotient_exists_generating_tuple k U hU hdegree π hπ
  exact firstCohomology_card_le_generator_power A (binaryCumulativeWidth k) g hg

end SymmetricSubgroupAsymptotics
