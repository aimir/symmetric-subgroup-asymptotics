import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenInterfaces

/-!
# Selected literal sixteen-point orbit witness

Source: `formal/SymmetricSubgroupAsymptotics/PrimitiveAffineDegreeTwoZeroSixteenInterfaces.lean`
Source SHA-256: `5a0381370c38934a80a387f21079a9d32cf01ba80e5453c7c9ba3670dae96fc1`
Selection: row 14, generator word [0, 2] (zero based).
Only the sixteen displayed point equalities are decided below.
The output still requires a bounded Lean check. Quotient-socle bounds are separate.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenRow14OrbitWitness

def generatorFactor0 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row14.top :=
  ⟨Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row14Generators 0, Subgroup.subset_closure ⟨0, rfl⟩⟩

def generatorFactor1 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row14.top :=
  ⟨Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row14Generators 2, Subgroup.subset_closure ⟨2, rfl⟩⟩

def element : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row14.top :=
  generatorFactor0 * generatorFactor1

def representatives : Fin 4 → Fin 16 :=
  ![0, 1, 2, 3]

def orbitIndex : Fin 16 → Fin 4 :=
  ![0, 1, 2, 3, 0, 3, 1, 2, 2, 0, 3, 1, 0, 2, 3, 1]

def exponent : Fin 16 → Fin 16 :=
  ![0, 0, 0, 0, 3, 3, 3, 3, 1, 1, 1, 1, 2, 2, 2, 2]

def witness : LiteralCyclicOrbitWitness Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row14.top 4 where
  element := element
  representative := representatives
  orbitIndex := orbitIndex
  exponent := exponent
  point_eq := by decide +kernel

theorem natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row14.top (Fin 16)) 4 :=
  witness.uniform (ZMod 2)

end PrimitiveAffineDegreeTwoZeroSixteenRow14OrbitWitness
end SymmetricSubgroupAsymptotics

end
