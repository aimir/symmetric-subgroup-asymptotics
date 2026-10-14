import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenInterfaces

/-!
# Selected literal sixteen-point orbit witness

Source: `formal/SymmetricSubgroupAsymptotics/PrimitiveAffineDegreeTwoPrimitiveSixteenInterfaces.lean`
Source SHA-256: `83ddef8134465fb34ec9f9c51885a0aa96711914565ca49ff7b5fb0781944d67`
Selection: row 17, generator index 0 (zero based).
Only the sixteen displayed point equalities are decided below.
The output still requires a bounded Lean check. Quotient-socle bounds are separate.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPrimitiveSixteenRow17OrbitWitness

def element : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPrimitiveSixteenInterfaces.row17.top :=
  ⟨Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPrimitiveSixteenInterfaces.row17Generators 0, Subgroup.subset_closure ⟨0, rfl⟩⟩

def representatives : Fin 4 → Fin 16 :=
  ![0, 1, 2, 5]

def orbitIndex : Fin 16 → Fin 4 :=
  ![0, 1, 2, 2, 1, 3, 2, 1, 1, 2, 1, 3, 3, 3, 2, 3]

def exponent : Fin 16 → Fin 16 :=
  ![0, 0, 0, 1, 4, 0, 4, 2, 3, 2, 1, 1, 4, 2, 3, 3]

def witness : LiteralCyclicOrbitWitness Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPrimitiveSixteenInterfaces.row17.top 4 where
  element := element
  representative := representatives
  orbitIndex := orbitIndex
  exponent := exponent
  point_eq := by decide +kernel

theorem natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPrimitiveSixteenInterfaces.row17.top (Fin 16)) 4 :=
  witness.uniform (ZMod 2)

end PrimitiveAffineDegreeTwoPrimitiveSixteenRow17OrbitWitness
end SymmetricSubgroupAsymptotics

end
