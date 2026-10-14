import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenInterfaces

/-!
# Selected literal sixteen-point orbit witness

Source: `formal/SymmetricSubgroupAsymptotics/PrimitiveAffineDegreeTwoZeroSixteenInterfaces.lean`
Source SHA-256: `5a0381370c38934a80a387f21079a9d32cf01ba80e5453c7c9ba3670dae96fc1`
Selection: row 6, generator word [2, 3] (zero based).
Only the sixteen displayed point equalities are decided below.
The output still requires a bounded Lean check. Quotient-socle bounds are separate.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenRow6OrbitWitness

def generatorFactor0 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row6.top :=
  ⟨Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row6Generators 2, Subgroup.subset_closure ⟨2, rfl⟩⟩

def generatorFactor1 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row6.top :=
  ⟨Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row6Generators 3, Subgroup.subset_closure ⟨3, rfl⟩⟩

def element : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row6.top :=
  generatorFactor0 * generatorFactor1

def representatives : Fin 4 → Fin 16 :=
  ![0, 1, 8, 10]

def orbitIndex : Fin 16 → Fin 4 :=
  ![0, 1, 1, 0, 0, 1, 0, 1, 2, 2, 3, 3, 2, 3, 2, 3]

def exponent : Fin 16 → Fin 16 :=
  ![0, 0, 2, 2, 1, 3, 3, 1, 0, 2, 0, 2, 1, 3, 3, 1]

def witness : LiteralCyclicOrbitWitness Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row6.top 4 where
  element := element
  representative := representatives
  orbitIndex := orbitIndex
  exponent := exponent
  point_eq := by decide +kernel

theorem natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row6.top (Fin 16)) 4 :=
  witness.uniform (ZMod 2)

end PrimitiveAffineDegreeTwoZeroSixteenRow6OrbitWitness
end SymmetricSubgroupAsymptotics

end
