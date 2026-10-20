import SymmetricSubgroupAsymptotics.FiniteBinaryNestedQuotientNonfixed
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow6NaturalModule
import SymmetricSubgroupAsymptotics.BinaryCoordinateDisplacementContainment
import SymmetricSubgroupAsymptotics.RepresentationSelfDualNestedQuotient
import SymmetricSubgroupAsymptotics.DualGeneratorSchurCapacity
import SymmetricSubgroupAsymptotics.Non2SchurRowDegrees
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopQuotientGeneratorData
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightTop6

/-! Generated finite table for paired8-6. Kernel reduction checks
orthogonals, basis displacements and every nested-pair step; the generic
dimension induction supplies every nonfixed certificate. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPairedEightRow6QuotientGenerators


abbrev Top := SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow6NaturalModule.Top
abbrev ModelModule := SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow6NaturalModule.ModelModule
abbrev representation := SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow6NaturalModule.representation
abbrev states := SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow6NaturalModule.states
abbrev charts := SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow6NaturalModule.charts

/-- State index of the standard-coordinate orthogonal complement. -/
def orthogonalState (i : Fin 11) : Fin 11 :=
  (#[10, 9, 8, 7, 4, 5, 6, 3, 2, 1, 0] : Array (Fin 11))[i.val]!

/-- The permutation-module self-duality is the ordinary coordinate dot
product. -/
theorem selfDual_apply (v w : ModelModule) :
    permutationFunctionRepresentationSelfDual (G := Top) v w =
      ∑ x, v x * w x :=
  permutationFunctionRepresentationSelfDual_apply (G := Top) v w

/-- Literal orthogonal-complement table for all invariant states. -/
theorem orthogonalState_eq (i : Fin 11) :
    selfDualOrthogonalSubrepresentation representation
        permutationFunctionRepresentationSelfDual (states i) =
      states (orthogonalState i) := by
  apply Subrepresentation.toSubmodule_injective
  ext v
  change (permutationFunctionRepresentationSelfDual (G := Top) v ∈
      (states i).toSubmodule.dualAnnihilator) ↔
    v ∈ (states (orthogonalState i)).toSubmodule
  rw [SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow6NaturalModule.states_space, SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow6NaturalModule.states_space, BinaryCoordinateSpace.mem_dualAnnihilator_iff_basis]
  simp only [selfDual_apply]
  fin_cases i <;> decide +kernel +revert

/-- The finite inclusion test uses only the displayed basis vectors. -/
private def stateLE (i j : Fin 11) : Prop :=
  ∀ a : Fin (charts i).1,
    (charts i).2.inclusion (Pi.single a 1) ∈ (charts j).2.space

private theorem state_le_iff (i j : Fin 11) :
    states i ≤ states j ↔ stateLE i j := by
  change (states i).toSubmodule ≤ (states j).toSubmodule ↔ _
  rw [PrimitiveAffineDegreeTwoPairedEightRow6NaturalModule.states_space,
    PrimitiveAffineDegreeTwoPairedEightRow6NaturalModule.states_space]
  constructor
  · exact fun h a ↦ h ⟨Pi.single a 1, rfl⟩
  · exact fun h ↦ (charts i).2.le_of_basis_mem _ h

private def displacementState (i : Fin 11) : Fin 11 :=
  (#[0, 0, 1, 3, 3, 3, 3, 3, 8, 8, 9] : Array (Fin 11))[i.val]!

/-- The retained-generator basis test controls every displacement. -/
private theorem displacement_mem (j : Fin 11) (g : Top) (v : ModelModule)
    (hv : v ∈ states j) :
    representation g v - v ∈ states (displacementState j) := by
  apply binaryCoordinate_displacements_mem_of_generator_basis representation
    PrimitiveAffineDegreeTwoPairedEightRow6NaturalModule.topAmbient
    PrimitiveAffineDegreeTwoPairedEightRow6NaturalModule.topAmbient_full (states j)
    (states (displacementState j)).toSubmodule (charts j).2
    (PrimitiveAffineDegreeTwoPairedEightRow6NaturalModule.states_space j) ?_ g v hv
  rw [PrimitiveAffineDegreeTwoPairedEightRow6NaturalModule.states_space]
  fin_cases j <;> decide +kernel +revert

/-- One checked table covers every nested pair. The general dimension
induction handles fixed upper layers without exceptional row proofs. -/
noncomputable def finiteTable :
    FiniteBinaryNestedQuotientNonfixedData
      PrimitiveAffineDegreeTwoPairedEightRow6NaturalModule.registry
      (permutationFunctionRepresentationSelfDual (G := Top)) where
  orthogonalState := orthogonalState
  orthogonalState_eq := orthogonalState_eq
  stateDimension := fun i ↦ (charts i).1
  state_finrank := by
    intro i
    rw [PrimitiveAffineDegreeTwoPairedEightRow6NaturalModule.states_space,
      (charts i).2.finrank]
  displacementState := displacementState
  displacement_mem := displacement_mem
  step := by
    intro i j hij
    have hchecked :
        (∃ c : Fin 10,
          PrimitiveAffineDegreeTwoPairedEightRow6NaturalModule.child
            (orthogonalState j) c = orthogonalState i) ∨
        (charts j).1 ≤ (charts i).1 + 2 ∨
        ∃ k : Fin 11, stateLE i k ∧ stateLE k j ∧
          stateLE (displacementState j) k ∧
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
        Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top6 where
  certificate := finiteTable.subrepresentation_certificate _ _

end PrimitiveAffineDegreeTwoPairedEightRow6QuotientGenerators
end SymmetricSubgroupAsymptotics

end
