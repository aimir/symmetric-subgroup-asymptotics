import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenInterfaces

/-!
# Selected literal sixteen-point orbit witness

Source: `formal/SymmetricSubgroupAsymptotics/PrimitiveAffineDegreeTwoPrimitiveSixteenInterfaces.lean`
Source SHA-256: `83ddef8134465fb34ec9f9c51885a0aa96711914565ca49ff7b5fb0781944d67`
Selection: row 11, generator index 0 (zero based).
Only the sixteen displayed point equalities are decided below.
The output still requires a bounded Lean check. Quotient-socle bounds are separate.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPrimitiveSixteenRow11OrbitWitness

def element : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPrimitiveSixteenInterfaces.row11.top :=
  ⟨Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPrimitiveSixteenInterfaces.row11Generators 0, Subgroup.subset_closure ⟨0, rfl⟩⟩

def representatives : Fin 4 → Fin 16 :=
  ![0, 1, 3, 8]

def orbitIndex : Fin 16 → Fin 4 :=
  ![0, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 1, 2, 1, 1, 2]

def exponent : Fin 16 → Fin 16 :=
  ![0, 0, 6, 0, 5, 4, 6, 2, 0, 3, 2, 4, 1, 1, 3, 5]

def witness : LiteralCyclicOrbitWitness Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPrimitiveSixteenInterfaces.row11.top 4 where
  element := element
  representative := representatives
  orbitIndex := orbitIndex
  exponent := exponent
  point_eq := by decide +kernel

theorem natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPrimitiveSixteenInterfaces.row11.top (Fin 16)) 4 :=
  witness.uniform (ZMod 2)

end PrimitiveAffineDegreeTwoPrimitiveSixteenRow11OrbitWitness
end SymmetricSubgroupAsymptotics

end
