import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenInterfaces

/-!
# Selected literal sixteen-point orbit witness

Source: `formal/SymmetricSubgroupAsymptotics/PrimitiveAffineDegreeTwoZeroSixteenInterfaces.lean`
Source SHA-256: `5a0381370c38934a80a387f21079a9d32cf01ba80e5453c7c9ba3670dae96fc1`
Selection: row 18, generator index 3 (zero based).
Only the sixteen displayed point equalities are decided below.
The output still requires a bounded Lean check. Quotient-socle bounds are separate.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenRow18OrbitWitness

def element : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row18.top :=
  ⟨Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row18Generators 3, Subgroup.subset_closure ⟨3, rfl⟩⟩

def representatives : Fin 4 → Fin 16 :=
  ![0, 1, 4, 6]

def orbitIndex : Fin 16 → Fin 4 :=
  ![0, 1, 0, 1, 2, 2, 3, 3, 1, 0, 0, 1, 2, 2, 3, 3]

def exponent : Fin 16 → Fin 16 :=
  ![0, 0, 2, 2, 0, 2, 0, 2, 3, 1, 3, 1, 1, 3, 3, 1]

def witness : LiteralCyclicOrbitWitness Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row18.top 4 where
  element := element
  representative := representatives
  orbitIndex := orbitIndex
  exponent := exponent
  point_eq := by decide +kernel

theorem natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row18.top (Fin 16)) 4 :=
  witness.uniform (ZMod 2)

end PrimitiveAffineDegreeTwoZeroSixteenRow18OrbitWitness
end SymmetricSubgroupAsymptotics

end
