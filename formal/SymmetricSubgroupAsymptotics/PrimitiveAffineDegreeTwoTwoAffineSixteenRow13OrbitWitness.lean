import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenInterfaces

/-!
# Selected literal sixteen-point orbit witness

Source: `formal/SymmetricSubgroupAsymptotics/PrimitiveAffineDegreeTwoTwoAffineSixteenInterfaces.lean`
Source SHA-256: `870d59ac561803ef98a859e4b00a2dc3e35516eb4938d463f6160f1006c0b98b`
Selection: row 13, generator index 11 (zero based).
Only the sixteen displayed point equalities are decided below.
The output still requires a bounded Lean check. Quotient-socle bounds are separate.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRow13OrbitWitness

def element : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwoAffineSixteenInterfaces.row13.top :=
  ⟨Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwoAffineSixteenInterfaces.row13Generators 11, Subgroup.subset_closure ⟨11, rfl⟩⟩

def representatives : Fin 4 → Fin 16 :=
  ![0, 1, 2, 3]

def orbitIndex : Fin 16 → Fin 4 :=
  ![0, 1, 2, 3, 3, 2, 1, 0, 0, 1, 3, 2, 2, 3, 1, 0]

def exponent : Fin 16 → Fin 16 :=
  ![0, 0, 0, 0, 2, 2, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3]

def witness : LiteralCyclicOrbitWitness Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwoAffineSixteenInterfaces.row13.top 4 where
  element := element
  representative := representatives
  orbitIndex := orbitIndex
  exponent := exponent
  point_eq := by decide +kernel

theorem natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwoAffineSixteenInterfaces.row13.top (Fin 16)) 4 :=
  witness.uniform (ZMod 2)

end PrimitiveAffineDegreeTwoTwoAffineSixteenRow13OrbitWitness
end SymmetricSubgroupAsymptotics

end
