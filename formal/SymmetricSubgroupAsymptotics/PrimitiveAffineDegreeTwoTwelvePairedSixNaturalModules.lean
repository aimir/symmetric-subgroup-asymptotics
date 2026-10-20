import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCataloguePairedSixInterfaces
import SymmetricSubgroupAsymptotics.PermutationPolynomialOrbitGenerators

/-!
# The two literal six-point modules have cyclic subrepresentations

The first cubic generator followed by the displayed block swap is a
six-cycle in both literal actions. The polynomial orbit-cover theorem
therefore handles every original invariant subspace over any field.
Only six point identities are checked; no group or submodule list is used.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelvePairedSixNaturalModules

open DegreeTwoTwelvePairFiniteCatalogue

def firstCycle : PairedSix1Top :=
  ⟨pairedSix1Generators 0 * pairedSix1Generators 2,
    Subgroup.mul_mem _ (Subgroup.subset_closure ⟨0, rfl⟩)
      (Subgroup.subset_closure ⟨2, rfl⟩)⟩

def secondCycle : PairedSix2Top :=
  ⟨pairedSix2Generators 0 * pairedSix2Generators 2,
    Subgroup.mul_mem _ (Subgroup.subset_closure ⟨0, rfl⟩)
      (Subgroup.subset_closure ⟨2, rfl⟩)⟩

theorem firstCycle_cover : ∀ x : Fin 6,
    ∃ m : Fin 6, firstCycle ^ m.val • (0 : Fin 6) = x := by
  decide +kernel

theorem secondCycle_cover : ∀ x : Fin 6,
    ∃ m : Fin 6, secondCycle ^ m.val • (0 : Fin 6) = x := by
  decide +kernel

theorem first_uniform (k : Type) [Field k] :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation k PairedSix1Top (Fin 6)) 1 := by
  apply permutationFunctionRepresentation_uniform_of_polynomial_orbitCover
    firstCycle (fun _ : Fin 1 ↦ (0 : Fin 6))
  intro x
  obtain ⟨m, hm⟩ := firstCycle_cover x
  exact ⟨0, m.val, hm⟩

theorem second_uniform (k : Type) [Field k] :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation k PairedSix2Top (Fin 6)) 1 := by
  apply permutationFunctionRepresentation_uniform_of_polynomial_orbitCover
    secondCycle (fun _ : Fin 1 ↦ (0 : Fin 6))
  intro x
  obtain ⟨m, hm⟩ := secondCycle_cover x
  exact ⟨0, m.val, hm⟩

end DegreeTwoTwelvePairedSixNaturalModules
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
