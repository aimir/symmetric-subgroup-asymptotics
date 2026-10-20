import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenInterfaces

/-!
# Selected literal sixteen-point orbit witness

Source: `formal/SymmetricSubgroupAsymptotics/PrimitiveAffineDegreeTwoPrimitiveSixteenInterfaces.lean`
Source SHA-256: `83ddef8134465fb34ec9f9c51885a0aa96711914565ca49ff7b5fb0781944d67`
Selection: row 10, generator word [2, 4] (zero based).
Only the sixteen displayed point equalities are decided below.
The output still requires a bounded Lean check. Quotient-socle bounds are separate.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPrimitiveSixteenRow10OrbitWitness

def generatorFactor0 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPrimitiveSixteenInterfaces.row10.top :=
  ⟨Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPrimitiveSixteenInterfaces.row10Generators 2, Subgroup.subset_closure ⟨2, rfl⟩⟩

def generatorFactor1 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPrimitiveSixteenInterfaces.row10.top :=
  ⟨Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPrimitiveSixteenInterfaces.row10Generators 4, Subgroup.subset_closure ⟨4, rfl⟩⟩

def element : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPrimitiveSixteenInterfaces.row10.top :=
  generatorFactor0 * generatorFactor1

def representatives : Fin 4 → Fin 16 :=
  ![0, 2, 3, 8]

def orbitIndex : Fin 16 → Fin 4 :=
  ![0, 0, 1, 2, 0, 0, 1, 2, 3, 3, 2, 1, 3, 3, 2, 1]

def exponent : Fin 16 → Fin 16 :=
  ![0, 3, 0, 0, 2, 1, 2, 2, 0, 3, 1, 3, 2, 1, 3, 1]

def witness : LiteralCyclicOrbitWitness Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPrimitiveSixteenInterfaces.row10.top 4 where
  element := element
  representative := representatives
  orbitIndex := orbitIndex
  exponent := exponent
  point_eq := by decide +kernel

theorem natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPrimitiveSixteenInterfaces.row10.top (Fin 16)) 4 :=
  witness.uniform (ZMod 2)

end PrimitiveAffineDegreeTwoPrimitiveSixteenRow10OrbitWitness
end SymmetricSubgroupAsymptotics

end
