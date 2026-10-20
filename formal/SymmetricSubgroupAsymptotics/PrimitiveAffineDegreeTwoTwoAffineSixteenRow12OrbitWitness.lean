import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenInterfaces

/-!
# Selected literal sixteen-point orbit witness

Source: `formal/SymmetricSubgroupAsymptotics/PrimitiveAffineDegreeTwoTwoAffineSixteenInterfaces.lean`
Source SHA-256: `870d59ac561803ef98a859e4b00a2dc3e35516eb4938d463f6160f1006c0b98b`
Selection: row 12, generator word [3, 4] (zero based).
Only the sixteen displayed point equalities are decided below.
The output still requires a bounded Lean check. Quotient-socle bounds are separate.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRow12OrbitWitness

def generatorFactor0 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwoAffineSixteenInterfaces.row12.top :=
  ⟨Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwoAffineSixteenInterfaces.row12Generators 3, Subgroup.subset_closure ⟨3, rfl⟩⟩

def generatorFactor1 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwoAffineSixteenInterfaces.row12.top :=
  ⟨Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwoAffineSixteenInterfaces.row12Generators 4, Subgroup.subset_closure ⟨4, rfl⟩⟩

def element : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwoAffineSixteenInterfaces.row12.top :=
  generatorFactor0 * generatorFactor1

def representatives : Fin 4 → Fin 16 :=
  ![0, 1, 8, 11]

def orbitIndex : Fin 16 → Fin 4 :=
  ![0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2]

def exponent : Fin 16 → Fin 16 :=
  ![0, 0, 1, 5, 6, 4, 2, 3, 0, 3, 2, 0, 5, 4, 6, 1]

def witness : LiteralCyclicOrbitWitness Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwoAffineSixteenInterfaces.row12.top 4 where
  element := element
  representative := representatives
  orbitIndex := orbitIndex
  exponent := exponent
  point_eq := by decide +kernel

theorem natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwoAffineSixteenInterfaces.row12.top (Fin 16)) 4 :=
  witness.uniform (ZMod 2)

end PrimitiveAffineDegreeTwoTwoAffineSixteenRow12OrbitWitness
end SymmetricSubgroupAsymptotics

end
