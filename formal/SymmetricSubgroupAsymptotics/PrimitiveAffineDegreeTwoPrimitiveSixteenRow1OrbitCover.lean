import SymmetricSubgroupAsymptotics.PermutationCyclicOrbitCoverGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenInterfaces

/-!
# A four-orbit Maschke certificate for primitive16 row 1

The first displayed generator has order five, with cycles of lengths
`1,5,5,5`. The only finite checks below concern this permutation and the
sixteen original points. Maschke supplies all invariant-subspace bounds.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPrimitiveSixteenRow1OrbitCover

abbrev Top := Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPrimitiveSixteenInterfaces.Row1Top

/-- The literal first generator, with its membership in the original top. -/
def generator : Top :=
  ⟨Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPrimitiveSixteenInterfaces.row1Generators 0, Subgroup.subset_closure ⟨0, rfl⟩⟩

private theorem generator_pow_five : generator ^ 5 = 1 := by
  apply Subtype.ext
  change (Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPrimitiveSixteenInterfaces.row1Generators 0) ^ 5 = 1
  decide +kernel

private theorem generator_ne_one : generator ≠ 1 := by
  have h : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPrimitiveSixteenInterfaces.row1Generators 0 ≠ 1 := by decide +kernel
  intro heq
  exact h (congrArg Subtype.val heq)

/-- The cyclic restriction has invertible order in characteristic two. -/
theorem generator_order : orderOf generator = 5 := by
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact orderOf_eq_prime generator_pow_five generator_ne_one

/-- One point in each of the generator's four orbits. -/
def representatives : Fin 4 → Fin 16 := ![0, 1, 3, 5]

private theorem orbit_cover_five : ∀ x : Fin 16,
    ∃ (j : Fin 4) (m : Fin 5),
      ((Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPrimitiveSixteenInterfaces.row1Generators 0) ^ m.val) (representatives j) = x := by
  decide +kernel

/-- Uniform natural-module bound from the order-five, four-orbit witness. -/
theorem natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) Top (Fin 16)) 4 := by
  apply permutationFunctionRepresentation_uniform_of_cyclic_orbitCover
    generator (by rw [generator_order]; exact (by decide +kernel : (5 : ZMod 2) ≠ 0))
    representatives
  intro x
  obtain ⟨j, m, hm⟩ := orbit_cover_five x
  exact ⟨j, m.val, hm⟩

/-- The same bound at the literal finite-interface boundary. -/
theorem interface_natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPrimitiveSixteenInterfaces.row1.top (Fin 16)) 4 :=
  natural

end PrimitiveAffineDegreeTwoPrimitiveSixteenRow1OrbitCover
end SymmetricSubgroupAsymptotics

end
