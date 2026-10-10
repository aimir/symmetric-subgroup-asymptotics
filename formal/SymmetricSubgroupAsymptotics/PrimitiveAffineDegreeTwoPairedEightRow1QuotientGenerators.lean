import SymmetricSubgroupAsymptotics.BinaryInvariantCyclicQuotientGenerator
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule
import SymmetricSubgroupAsymptotics.RepresentationSelfDualNestedQuotient
import SymmetricSubgroupAsymptotics.DualGeneratorSchurCapacity
import SymmetricSubgroupAsymptotics.Non2SchurRowDegrees

/-!
# Dual generators for paired-eight state quotients

The eleven invariant states of the paired-eight natural module are closed
under orthogonal complement for the standard coordinate pairing.  Reversing
a nested pair by this involution turns every state quotient except one
two-dimensional plane into a single edge of the checked cyclic child table.
Consequently the dual of every nonexceptional nested quotient is generated
by one element.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPairedEightRow1QuotientGenerators

namespace Natural := PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule

abbrev Top := Natural.Top
abbrev ModelModule := Natural.ModelModule
abbrev representation := Natural.representation
abbrev states := Natural.states
abbrev charts := Natural.charts

/-- State index of the standard-coordinate orthogonal complement. -/
def orthogonalState (i : Fin 11) : Fin 11 :=
  (#[10, 9, 8, 7, 4, 5, 6, 3, 2, 1, 0] : Array (Fin 11))[i.val]!

/-- The permutation-module self-duality is the ordinary coordinate dot
product. -/
theorem selfDual_apply (v w : ModelModule) :
    permutationFunctionRepresentationSelfDual v w =
      ∑ x, v x * w x := by
  simp only [permutationFunctionRepresentationSelfDual,
    Basis.toDualEquiv_apply, Basis.toDual_apply_left,
    Pi.basisFun_repr, Finsupp.linearCombination_apply,
    Finsupp.sum_fintype, Pi.basisFun_apply, Pi.single_apply]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-- Literal orthogonal-complement table for all eleven invariant states. -/
theorem orthogonalState_eq (i : Fin 11) :
    selfDualOrthogonalSubrepresentation representation
        permutationFunctionRepresentationSelfDual (states i) =
      states (orthogonalState i) := by
  apply Subrepresentation.toSubmodule_injective
  ext v
  rw [selfDualOrthogonalSubrepresentation, Submodule.mem_comap,
    Submodule.mem_dualAnnihilator, Natural.states_space,
    Natural.states_space]
  simp only [selfDual_apply]
  fin_cases i <;> native_decide +revert

/-- The unique nested quotient whose reversed orthogonal quotient needs two
generators is `state 8 / state 4`; every other nonzero nested quotient is one
checked cyclic child-table edge. -/
theorem dualChild_exists_of_le_of_not_exception
    (i j : Fin 11) (hij : states i ≤ states j)
    (hexception : ¬ (i = 4 ∧ j = 8)) :
    ∃ c : Fin 10,
      Natural.child (orthogonalState j) c = orthogonalState i := by
  rw [Natural.states_space, Natural.states_space] at hij
  fin_cases i <;> fin_cases j <;> native_decide +revert

/-- Every nonexceptional paired-eight state quotient has cyclic dual. -/
theorem nestedQuotient_dual_generated
    (i j : Fin 11) (hij : states i ≤ states j)
    (hexception : ¬ (i = 4 ∧ j = 8)) :
    RepresentationGeneratedBy
      (nestedQuotientRepresentation (states i) (states j) hij).dual 1 := by
  obtain ⟨c, hc⟩ :=
    dualChild_exists_of_le_of_not_exception i j hij hexception
  let e := permutationFunctionRepresentationSelfDual
  let horth := selfDualOrthogonalSubrepresentation_antitone
    representation e hij
  have hstate : states (orthogonalState j) ≤
      states (orthogonalState i) := by
    rw [← orthogonalState_eq, ← orthogonalState_eq]
    exact horth
  have hgen : RepresentationGeneratedBy
      (nestedQuotientRepresentation
        (states (orthogonalState j))
        (states (orthogonalState i)) hstate) 1 := by
    simpa only [hc, BinaryInvariantCyclicOrbitRegistry.childQuotientRepresentation,
      BinaryInvariantCyclicOrbitRegistry.childDenominator,
      nestedQuotientRepresentation, nestedSubrepresentation] using
        Natural.registry.childQuotientRepresentation_generated
          (orthogonalState j) c
  have hgenOrth : RepresentationGeneratedBy
      (nestedQuotientRepresentation
        (selfDualOrthogonalSubrepresentation representation e (states j))
        (selfDualOrthogonalSubrepresentation representation e (states i))
        horth) 1 := by
    simpa only [e, orthogonalState_eq] using hgen
  let E := selfDualNestedQuotientEquiv representation e
    (states i) (states j) hij
  have htransport := representationGeneratedBy_of_surjective
    _ _ E.toIntertwiningMap E.surjective hgenOrth
  exact htransport

/-- The exceptional reversed quotient is exactly a binary plane. -/
theorem exceptional_finrank_le_two
    (h48 : states (4 : Fin 11) ≤ states (8 : Fin 11)) :
    Module.finrank (ZMod 2)
      (nestedQuotientRepresentation (states 4) (states 8) h48).asModule ≤ 2 := by
  change Module.finrank (ZMod 2)
      ((states 8).toSubmodule ⧸
        (nestedSubrepresentation (states 4) (states 8) h48).toSubmodule) ≤ 2
  have hquot :=
    (nestedSubrepresentation (states 4) (states 8) h48).toSubmodule.
      finrank_quotient_add_finrank
  have hden := finrank_nestedSubrepresentation
    (states 4) (states 8) h48
  have hfour : Module.finrank (ZMod 2) (states 4).toSubmodule = 4 := by
    rw [Natural.states_space, (charts 4).2.finrank]
  have hsix : Module.finrank (ZMod 2) (states 8).toSubmodule = 6 := by
    rw [Natural.states_space, (charts 8).2.finrank]
  rw [hden, hfour, hsix] at hquot
  omega

/-- Uniform finite-state conclusion: every nonfixed simple row in every
nested paired-eight state quotient is bounded by one dual-generator layer,
namely its dimension over its Schur division ring.  The ordinary cases use
the cyclic dual certificate; the unique exceptional case is even smaller,
because its target is a literal binary plane. -/
theorem nestedQuotient_nonfixed_schurSocleMultiplicity_le_end_finrank
    (i j : Fin 11) (hij : states i ≤ states j)
    {A : Type*} [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
    (sigma : Representation (ZMod 2) Top A)
    (S : Submodule (ZMod 2)[Top] sigma.asModule)
    [Finite S] [IsSimpleModule (ZMod 2)[Top] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S) :
    schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[Top])
        (A := (nestedQuotientRepresentation
          (states i) (states j) hij).asModule) (X := S) ≤
      Module.finrank (Module.End (ZMod 2)[Top] S) S := by
  letI : FiniteDimensional (ZMod 2) A :=
    Module.Finite.of_finite (ZMod 2) A
  letI : FiniteDimensional (ZMod 2) S :=
    Module.Finite.of_finite (ZMod 2) S
  by_cases hexception : i = 4 ∧ j = 8
  · obtain ⟨rfl, rfl⟩ := hexception
    have hone := schurSocleMultiplicity_le_one_of_finrank_le_two_of_nonfixed
      sigma S hnonfixed (exceptional_finrank_le_two hij)
    have hpos : 0 < Module.finrank (Module.End (ZMod 2)[Top] S) S := by
      letI : Nontrivial S := IsSimpleModule.nontrivial (ZMod 2)[Top] S
      exact Module.finrank_pos
        (R := Module.End (ZMod 2)[Top] S) (M := S)
    exact hone.trans hpos
  · have hgen := nestedQuotient_dual_generated i j hij hexception
    have hschur := schurSocleMultiplicity_le_of_dual_generated
      (nestedQuotientRepresentation (states i) (states j) hij) 1 hgen
      (X := S)
    simpa only [one_mul] using hschur

end PrimitiveAffineDegreeTwoPairedEightRow1QuotientGenerators
end SymmetricSubgroupAsymptotics

end
