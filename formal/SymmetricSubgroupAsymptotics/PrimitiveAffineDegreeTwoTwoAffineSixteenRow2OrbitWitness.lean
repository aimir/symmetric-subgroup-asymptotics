import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenInterfaces

/-!
# Selected literal sixteen-point orbit witness

Source: `formal/SymmetricSubgroupAsymptotics/PrimitiveAffineDegreeTwoTwoAffineSixteenInterfaces.lean`
Source SHA-256: `870d59ac561803ef98a859e4b00a2dc3e35516eb4938d463f6160f1006c0b98b`
Selection: row 2, generator index 9 (zero based).
Only the sixteen displayed point equalities are decided below.
The output still requires a bounded Lean check. Quotient-socle bounds are separate.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRow2OrbitWitness

def element : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwoAffineSixteenInterfaces.row2.top :=
  ⟨Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwoAffineSixteenInterfaces.row2Generators 9, Subgroup.subset_closure ⟨9, rfl⟩⟩

def representatives : Fin 4 → Fin 16 :=
  ![0, 1, 8, 9]

def orbitIndex : Fin 16 → Fin 4 :=
  ![0, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 3, 3, 3]

def exponent : Fin 16 → Fin 16 :=
  ![0, 0, 5, 4, 3, 1, 2, 6, 0, 0, 5, 4, 3, 1, 2, 6]

def witness : LiteralCyclicOrbitWitness Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwoAffineSixteenInterfaces.row2.top 4 where
  element := element
  representative := representatives
  orbitIndex := orbitIndex
  exponent := exponent
  point_eq := by decide +kernel

theorem natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwoAffineSixteenInterfaces.row2.top (Fin 16)) 4 :=
  witness.uniform (ZMod 2)

end PrimitiveAffineDegreeTwoTwoAffineSixteenRow2OrbitWitness
end SymmetricSubgroupAsymptotics

end
