import SymmetricSubgroupAsymptotics.BinaryFourTernaryKleinOperator
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250

/-! Five literal four-ternary-block actions share one two-generator
polynomial certificate. Each conclusion retains the original top,
the original twelve-point action, and the stored capacity two. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveTernaryKleinNaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def pointChart (j : Fin 3) : Equiv.Perm (Fin 12) where
  toFun x := ((#[
    #[0, 1, 3, 10, 4, 9, 7, 6, 8, 5, 11, 2],
    #[3, 6, 1, 4, 7, 10, 9, 0, 11, 2, 5, 8],
    #[3, 6, 1, 0, 7, 10, 9, 4, 11, 2, 5, 8]
    ] : Array (Array (Fin 12)))[j.val]!)[x.val]!
  invFun x := ((#[
    #[0, 1, 11, 2, 4, 9, 7, 6, 8, 5, 3, 10],
    #[7, 2, 9, 0, 3, 10, 1, 4, 11, 6, 5, 8],
    #[3, 2, 9, 0, 7, 10, 1, 4, 11, 6, 5, 8]
    ] : Array (Array (Fin 12)))[j.val]!)[x.val]!
  left_inv := by revert j; decide +kernel
  right_inv := by revert j; decide +kernel

def row47Transports : Fin 4 → Row47Top :=
  ![1, closureGenerators row47Generators 2, closureGenerators row47Generators 3,
    closureGenerators row47Generators 2 * closureGenerators row47Generators 3]

def row171Transports : Fin 4 → Row171Top :=
  ![1, closureGenerators row171Generators 2, closureGenerators row171Generators 3,
    closureGenerators row171Generators 2 * closureGenerators row171Generators 3]

def row172Transports : Fin 4 → Row172Top :=
  ![1, closureGenerators row172Generators 2, closureGenerators row172Generators 3,
    closureGenerators row172Generators 2 * closureGenerators row172Generators 3]

def row174Transports : Fin 4 → Row174Top :=
  ![1, closureGenerators row174Generators 2, closureGenerators row174Generators 3,
    closureGenerators row174Generators 2 * closureGenerators row174Generators 3]

def row246Transports : Fin 4 → Row246Top :=
  ![1, closureGenerators row246Generators 2, closureGenerators row246Generators 3,
    closureGenerators row246Generators 2 * closureGenerators row246Generators 3]

theorem row47Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row47Interface.top (Fin 12)) 2 := by
  apply BinaryFourTernaryKleinOperator.uniform_of_basis false _
    (closureGenerators row47Generators 0) (closureGenerators row47Generators 2)
    row47Transports (pointChart 0)
  decide +kernel

theorem row171Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row171Interface.top (Fin 12)) 2 := by
  apply BinaryFourTernaryKleinOperator.uniform_of_basis true _
    (closureGenerators row171Generators 0) (closureGenerators row171Generators 2)
    row171Transports (pointChart 1)
  decide +kernel

theorem row172Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row172Interface.top (Fin 12)) 2 := by
  apply BinaryFourTernaryKleinOperator.uniform_of_basis true _
    (closureGenerators row172Generators 0) (closureGenerators row172Generators 2)
    row172Transports (pointChart 1)
  decide +kernel

theorem row174Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row174Interface.top (Fin 12)) 2 := by
  apply BinaryFourTernaryKleinOperator.uniform_of_basis true _
    (closureGenerators row174Generators 0) (closureGenerators row174Generators 2)
    row174Transports (pointChart 2)
  decide +kernel

theorem row246Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row246Interface.top (Fin 12)) 2 := by
  apply BinaryFourTernaryKleinOperator.uniform_of_basis true _
    (closureGenerators row246Generators 0) (closureGenerators row246Generators 2)
    row246Transports (pointChart 1)
  decide +kernel

end PrimitiveAffineDegreeTwoTwelveTernaryKleinNaturalFamily
end SymmetricSubgroupAsymptotics

end
