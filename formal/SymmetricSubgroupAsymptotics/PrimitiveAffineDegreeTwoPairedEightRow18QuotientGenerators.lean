import SymmetricSubgroupAsymptotics.FiniteBinaryNestedQuotientNonfixed
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow18NaturalModule
import SymmetricSubgroupAsymptotics.BinaryCoordinateDisplacementContainment
import SymmetricSubgroupAsymptotics.RepresentationSelfDualNestedQuotient
import SymmetricSubgroupAsymptotics.DualGeneratorSchurCapacity
import SymmetricSubgroupAsymptotics.Non2SchurRowDegrees
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopQuotientGeneratorData
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightAffineLiteralTops

/-! Generated finite table for paired8-18. Kernel reduction checks
orthogonals, basis displacements and every nested-pair step; the generic
dimension induction supplies every nonfixed certificate. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPairedEightRow18QuotientGenerators


abbrev Top := SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow18NaturalModule.Top
abbrev ModelModule := SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow18NaturalModule.ModelModule
abbrev representation := SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow18NaturalModule.representation
abbrev states := SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow18NaturalModule.states
abbrev charts := SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow18NaturalModule.charts

/-- State index of the standard-coordinate orthogonal complement. -/
def orthogonalState (i : Fin 5) : Fin 5 :=
  (#[4, 3, 2, 1, 0] : Array (Fin 5))[i.val]!

/-- The permutation-module self-duality is the ordinary coordinate dot
product. -/
theorem selfDual_apply (v w : ModelModule) :
    permutationFunctionRepresentationSelfDual (G := Top) v w =
      ∑ x, v x * w x :=
  permutationFunctionRepresentationSelfDual_apply (G := Top) v w

/-- Literal orthogonal-complement table for all invariant states. -/
theorem orthogonalState_eq (i : Fin 5) :
    selfDualOrthogonalSubrepresentation representation
        permutationFunctionRepresentationSelfDual (states i) =
      states (orthogonalState i) := by
  apply Subrepresentation.toSubmodule_injective
  ext v
  change (permutationFunctionRepresentationSelfDual (G := Top) v ∈
      (states i).toSubmodule.dualAnnihilator) ↔
    v ∈ (states (orthogonalState i)).toSubmodule
  rw [SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow18NaturalModule.states_space, SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow18NaturalModule.states_space, BinaryCoordinateSpace.mem_dualAnnihilator_iff_basis]
  simp only [selfDual_apply]
  fin_cases i <;> decide +kernel +revert

/-- The finite inclusion test uses only the displayed basis vectors. -/
private def stateLE (i j : Fin 5) : Prop :=
  ∀ a : Fin (charts i).1,
    (charts i).2.inclusion (Pi.single a 1) ∈ (charts j).2.space

private theorem state_le_iff (i j : Fin 5) :
    states i ≤ states j ↔ stateLE i j := by
  change (states i).toSubmodule ≤ (states j).toSubmodule ↔ _
  rw [PrimitiveAffineDegreeTwoPairedEightRow18NaturalModule.states_space,
    PrimitiveAffineDegreeTwoPairedEightRow18NaturalModule.states_space]
  constructor
  · exact fun h a ↦ h ⟨Pi.single a 1, rfl⟩
  · exact fun h ↦ (charts i).2.le_of_basis_mem _ h

private def displacementState (i : Fin 5) : Fin 5 :=
  (#[0, 0, 2, 3, 3] : Array (Fin 5))[i.val]!

/-- The retained-generator basis test controls every displacement. -/
private theorem displacement_mem (j : Fin 5) (g : Top) (v : ModelModule)
    (hv : v ∈ states j) :
    representation g v - v ∈ states (displacementState j) := by
  apply binaryCoordinate_displacements_mem_of_generator_basis representation
    PrimitiveAffineDegreeTwoPairedEightRow18NaturalModule.topAmbient
    PrimitiveAffineDegreeTwoPairedEightRow18NaturalModule.topAmbient_full (states j)
    (states (displacementState j)).toSubmodule (charts j).2
    (PrimitiveAffineDegreeTwoPairedEightRow18NaturalModule.states_space j) ?_ g v hv
  rw [PrimitiveAffineDegreeTwoPairedEightRow18NaturalModule.states_space]
  fin_cases j <;> decide +kernel +revert

/-- One checked table covers every nested pair. The general dimension
induction handles fixed upper layers without exceptional row proofs. -/
noncomputable def finiteTable :
    FiniteBinaryNestedQuotientNonfixedData
      PrimitiveAffineDegreeTwoPairedEightRow18NaturalModule.registry
      (permutationFunctionRepresentationSelfDual (G := Top)) where
  orthogonalState := orthogonalState
  orthogonalState_eq := orthogonalState_eq
  stateDimension := fun i ↦ (charts i).1
  state_finrank := by
    intro i
    rw [PrimitiveAffineDegreeTwoPairedEightRow18NaturalModule.states_space,
      (charts i).2.finrank]
  displacementState := displacementState
  displacement_mem := displacement_mem
  step := by
    intro i j hij
    have hchecked :
        (∃ c : Fin 5,
          PrimitiveAffineDegreeTwoPairedEightRow18NaturalModule.child
            (orthogonalState j) c = orthogonalState i) ∨
        (charts j).1 ≤ (charts i).1 + 2 ∨
        ∃ k : Fin 5, stateLE i k ∧ stateLE k j ∧
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
        Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top18 where
  certificate := finiteTable.subrepresentation_certificate _ _

end PrimitiveAffineDegreeTwoPairedEightRow18QuotientGenerators
end SymmetricSubgroupAsymptotics

end
