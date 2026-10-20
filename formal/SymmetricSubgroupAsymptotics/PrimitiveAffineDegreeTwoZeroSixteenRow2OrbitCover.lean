import SymmetricSubgroupAsymptotics.PermutationPolynomialOrbitGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenInterfaces

/-!
# A four-orbit polynomial certificate for zero16 row 2

The second displayed generator has four cycles of length four. Delta
functions at their representatives generate over the polynomial ring,
and the PID theorem supplies the same bound for every invariant subspace.
The sole finite check concerns powers on the sixteen original points.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenRow2OrbitCover

abbrev Top := Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.Row2Top

/-- The literal second generator belongs to the original finite-interface top. -/
def generator : Top :=
  ⟨Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row2Generators 1, Subgroup.subset_closure ⟨1, rfl⟩⟩

/-- The representatives of `(0,11,3,10)`, `(1,9,2,8)`, `(4,15,6,13)`,
and `(5,14,7,12)`. -/
def representatives : Fin 4 → Fin 16 := ![0, 1, 4, 5]

private theorem orbit_cover_four : ∀ x : Fin 16,
    ∃ (j : Fin 4) (m : Fin 4),
      ((Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row2Generators 1) ^ m.val) (representatives j) = x := by
  decide +kernel

/-- A uniform four-generator bound even though the displayed acting
element has order divisible by the characteristic. -/
theorem natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) Top (Fin 16)) 4 := by
  apply permutationFunctionRepresentation_uniform_of_polynomial_orbitCover
    generator representatives
  intro x
  obtain ⟨j, m, hm⟩ := orbit_cover_four x
  exact ⟨j, m.val, hm⟩

/-- The bound at the literal finite-interface boundary. -/
theorem interface_natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row2.top (Fin 16)) 4 :=
  natural

end PrimitiveAffineDegreeTwoZeroSixteenRow2OrbitCover
end SymmetricSubgroupAsymptotics

end
