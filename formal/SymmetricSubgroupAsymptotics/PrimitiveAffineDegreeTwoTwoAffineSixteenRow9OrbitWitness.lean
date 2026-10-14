import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenInterfaces

/-!
# Selected literal sixteen-point orbit witness

Source: `formal/SymmetricSubgroupAsymptotics/PrimitiveAffineDegreeTwoTwoAffineSixteenInterfaces.lean`
Source SHA-256: `870d59ac561803ef98a859e4b00a2dc3e35516eb4938d463f6160f1006c0b98b`
Selection: row 9, generator index 13 (zero based).
Only the sixteen displayed point equalities are decided below.
The output still requires a bounded Lean check. Quotient-socle bounds are separate.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRow9OrbitWitness

def element : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwoAffineSixteenInterfaces.row9.top :=
  ⟨Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwoAffineSixteenInterfaces.row9Generators 13, Subgroup.subset_closure ⟨13, rfl⟩⟩

def representatives : Fin 4 → Fin 16 :=
  ![0, 1, 0, 0]

def orbitIndex : Fin 16 → Fin 4 :=
  ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

def exponent : Fin 16 → Fin 16 :=
  ![0, 0, 12, 8, 10, 2, 4, 6, 1, 5, 13, 11, 3, 9, 7, 1]

def witness : LiteralCyclicOrbitWitness Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwoAffineSixteenInterfaces.row9.top 4 where
  element := element
  representative := representatives
  orbitIndex := orbitIndex
  exponent := exponent
  point_eq := by decide +kernel

theorem natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwoAffineSixteenInterfaces.row9.top (Fin 16)) 4 :=
  witness.uniform (ZMod 2)

end PrimitiveAffineDegreeTwoTwoAffineSixteenRow9OrbitWitness
end SymmetricSubgroupAsymptotics

end
