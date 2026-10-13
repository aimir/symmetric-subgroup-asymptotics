import SymmetricSubgroupAsymptotics.FiniteBinaryNestedQuotientNonfixed
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads
import SymmetricSubgroupAsymptotics.RepresentationSelfDualNestedQuotient
import SymmetricSubgroupAsymptotics.DualGeneratorSchurCapacity
import SymmetricSubgroupAsymptotics.Non2SchurRowDegrees
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopQuotientGeneratorData
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightSharedTops

/-!
# Dual generators for paired-eight state quotients

The eleven invariant states of the paired-eight natural module are closed
under orthogonal complement for the standard coordinate pairing.  Reversing
a nested pair by this involution turns all but three state quotients into
single edges of the checked cyclic child table. The exceptions are the
quotients of states 7, 9 and 10 by state 3. The first has dimension two;
the latter two reduce to a cyclic-dual quotient by removing fixed upper
layers. The resulting nonfixed bound applies to every nested pair.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPairedEightRow1QuotientGenerators


abbrev Top := SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.Top
abbrev ModelModule := SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.ModelModule
abbrev representation := SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.representation
abbrev states := SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.states
abbrev charts := SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.charts

/-- State index of the standard-coordinate orthogonal complement. -/
def orthogonalState (i : Fin 11) : Fin 11 :=
  (#[10, 9, 8, 7, 4, 5, 6, 3, 2, 1, 0] : Array (Fin 11))[i.val]!

/-- The permutation-module self-duality is the ordinary coordinate dot
product. -/
theorem selfDual_apply (v w : ModelModule) :
    permutationFunctionRepresentationSelfDual (G := Top) v w =
      ∑ x, v x * w x :=
  permutationFunctionRepresentationSelfDual_apply (G := Top) v w

/-- Testing a linear functional on a coordinate basis suffices for the
whole annihilator. This keeps the finite test linear in the chart dimension. -/
private theorem chart_annihilator_mem_iff {w d : ℕ}
    (C : BinaryCoordinateSpace w d)
    (f : Module.Dual (ZMod 2) (Fin w → ZMod 2)) :
    f ∈ C.space.dualAnnihilator ↔
      ∀ j, f (C.inclusion (Pi.single j 1)) = 0 := by
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro h j
    exact h _ ⟨Pi.single j 1, rfl⟩
  · intro h v hv
    have hle : C.space ≤ LinearMap.ker f :=
      C.le_of_basis_mem _ (fun j ↦ h j)
    exact hle hv

/-- Literal orthogonal-complement table for all eleven invariant states. -/
theorem orthogonalState_eq (i : Fin 11) :
    selfDualOrthogonalSubrepresentation representation
        permutationFunctionRepresentationSelfDual (states i) =
      states (orthogonalState i) := by
  apply Subrepresentation.toSubmodule_injective
  ext v
  change (permutationFunctionRepresentationSelfDual (G := Top) v ∈
      (states i).toSubmodule.dualAnnihilator) ↔
    v ∈ (states (orthogonalState i)).toSubmodule
  rw [SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.states_space, SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.states_space, chart_annihilator_mem_iff]
  simp only [selfDual_apply]
  fin_cases i <;> decide +kernel +revert

/-- The finite inclusion test uses only the displayed basis vectors. -/
private def stateLE (i j : Fin 11) : Prop :=
  ∀ a : Fin (charts i).1,
    (charts i).2.inclusion (Pi.single a 1) ∈ (charts j).2.space

private theorem state_le_iff (i j : Fin 11) :
    states i ≤ states j ↔ stateLE i j := by
  change (states i).toSubmodule ≤ (states j).toSubmodule ↔ _
  rw [PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.states_space,
    PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.states_space]
  constructor
  · exact fun h a ↦ h ⟨Pi.single a 1, rfl⟩
  · exact fun h ↦ (charts i).2.le_of_basis_mem _ h

/-- The checked displacement table supplies the fixed upper-layer test. -/
private theorem displacement_mem (j : Fin 11) (g : Top) (v : ModelModule)
    (hv : v ∈ states j) :
    representation g v - v ∈ states (SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads.displacementState j) := by
  have hmem : representation g v - v ∈
      (Representation.Coinvariants.ker (states j).toRepresentation).map
        (states j).toSubmodule.subtype := by
    exact ⟨(states j).toRepresentation g ⟨v, hv⟩ - ⟨v, hv⟩,
      Representation.Coinvariants.sub_mem_ker g (⟨v, hv⟩ : (states j).toSubmodule), rfl⟩
  rwa [SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads.coinvariantsKernel_map_eq_state] at hmem

/-- One checked table covers every nested pair. The general dimension
induction handles fixed upper layers without exceptional row proofs. -/
noncomputable def finiteTable :
    FiniteBinaryNestedQuotientNonfixedData
      PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.registry
      (permutationFunctionRepresentationSelfDual (G := Top)) where
  orthogonalState := orthogonalState
  orthogonalState_eq := orthogonalState_eq
  stateDimension := fun i ↦ (charts i).1
  state_finrank := by
    intro i
    rw [PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.states_space,
      (charts i).2.finrank]
  displacementState := PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads.displacementState
  displacement_mem := displacement_mem
  step := by
    intro i j hij
    have hchecked :
        (∃ c : Fin 10,
          PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule.child
            (orthogonalState j) c = orthogonalState i) ∨
        (charts j).1 ≤ (charts i).1 + 2 ∨
        ∃ k : Fin 11, stateLE i k ∧ stateLE k j ∧
          stateLE (PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads.displacementState j) k ∧
          (charts k).1 < (charts j).1 := by
      have h := (state_le_iff i j).mp hij
      clear hij
      revert h
      unfold stateLE
      fin_cases i <;> fin_cases j <;> decide +kernel +revert
    rcases hchecked with hcyclic | hsmall | ⟨k, hik, hkj, hd, hdim⟩
    · exact Or.inl hcyclic
    · exact Or.inr (Or.inl hsmall)
    · exact Or.inr (Or.inr ⟨k, (state_le_iff i k).mpr hik,
        (state_le_iff k j).mpr hkj, (state_le_iff _ k).mpr hd, hdim⟩)

/-- Realization-free declaration obtained by the uniform finite-table
induction, including every fixed-layer descent. -/
noncomputable def finiteGeneratorData :
    Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairTopNestedQuotientGeneratorData
        Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 where
  certificate := finiteTable.subrepresentation_certificate _ _

/-- Uniform finite-state conclusion: every nonfixed simple row in every
nested paired-eight state quotient is bounded by one dual-generator layer,
namely its dimension over its Schur division ring. Ordinary cases use
the cyclic-dual certificate; the exceptions use a binary plane or certified
fixed upper layers. -/
theorem nestedQuotient_nonfixed_schurSocleMultiplicity_le_end_finrank
    (i j : Fin 11) (hij : states i ≤ states j)
    {A : Type} [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
    (sigma : Representation (ZMod 2) Top A)
    (S : Submodule (ZMod 2)[Top] sigma.asModule)
    [Finite S] [IsSimpleModule (ZMod 2)[Top] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S) :
    schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[Top])
        (A := (nestedQuotientRepresentation
          (states i) (states j) hij).asModule) (X := S) ≤
      Module.finrank (Module.End (ZMod 2)[Top] S) S := by
  exact finiteGeneratorData.subrepresentationQuotient_comp_nonfixed_le_end_finrank
    (MonoidHom.id Top) Function.surjective_id
    (states i) (states j) hij sigma S hnonfixed

/-- Catalogue-free semantic form of the finite theorem.  Completeness of
the eleven-state registry selects the two endpoints of an arbitrary nested
pair, after which the checked quotient table supplies the bound. -/
theorem subrepresentationQuotient_nonfixed_schurSocleMultiplicity_le_end_finrank
    (A B : Subrepresentation representation) (hAB : A ≤ B)
    {X : Type} [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (sigma : Representation (ZMod 2) Top X)
    (S : Submodule (ZMod 2)[Top] sigma.asModule)
    [Finite S] [IsSimpleModule (ZMod 2)[Top] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S) :
    schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[Top])
        (A := (nestedQuotientRepresentation A B hAB).asModule) (X := S) ≤
      Module.finrank (Module.End (ZMod 2)[Top] S) S := by
  exact finiteGeneratorData.subrepresentationQuotient_comp_nonfixed_le_end_finrank
    (MonoidHom.id Top) Function.surjective_id A B hAB sigma S hnonfixed

/-- The semantic quotient bound survives pullback along any surjective group
map.  This is the form consumed by an original pair action: the finite state
quotient lives over the literal top, while its action on the actual quotient
group is obtained by inflation. -/
theorem subrepresentationQuotient_comp_nonfixed_le_end_finrank
    {H X : Type} [Group H]
    (gamma : H →* Top) (hgamma : Function.Surjective gamma)
    (A B : Subrepresentation representation) (hAB : A ≤ B)
    [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (sigma : Representation (ZMod 2) H X)
    (S : Submodule (ZMod 2)[H] sigma.asModule)
    [Finite S] [IsSimpleModule (ZMod 2)[H] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S) :
    schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[H])
        (A := (inflatedRepresentation gamma (nestedQuotientRepresentation A B hAB)).asModule)
        (X := S) ≤
      Module.finrank (Module.End (ZMod 2)[H] S) S := by
  exact finiteGeneratorData.subrepresentationQuotient_comp_nonfixed_le_end_finrank
    gamma hgamma A B hAB sigma S hnonfixed

end PrimitiveAffineDegreeTwoPairedEightRow1QuotientGenerators
end SymmetricSubgroupAsymptotics

end
