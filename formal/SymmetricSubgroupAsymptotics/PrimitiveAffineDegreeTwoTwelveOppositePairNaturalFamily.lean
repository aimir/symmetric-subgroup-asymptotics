import SymmetricSubgroupAsymptotics.BinarySixPointSymmetricMatrixBlocks
import SymmetricSubgroupAsymptotics.BinaryPairFrameGenerators
import SymmetricSubgroupAsymptotics.BinaryPairPermutationGeneratorExtension
import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150

/-! Two original cap-two natural bounds use opposite physical pairs.
Row9 has the regular S3 six-point quotient, so the pair-sum exact sequence
doubles its uniform cyclic bound. Row103's local opposite-pair swap and
ternary shift directly give the same cyclic-orbit/PID bound on twelve points. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveOppositePairNaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open BinarySixPointSymmetricMatrixBlocks

def pointChart : Fin 6 × ZMod 2 ≃ Fin 12 where
  toFun p := if p.2 = 0 then ![0, 1, 2, 3, 4, 5] p.1 else ![6, 7, 8, 9, 10, 11] p.1
  invFun x := (![0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5] x,
    ![0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1] x)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pairReflection : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 5, 4, 3, 2]
  invFun := ![1, 0, 5, 4, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row9Tops : Fin 3 → Equiv.Perm (Fin 6) :=
  ![1, BinarySixPointSymmetricMatrixBlocks.rotation⁻¹, pairReflection]

theorem row9_preserves : ∀ i,
    BinaryPairFrame.Preserves pointChart (row9Generators i) (row9Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def row9Frame : BinaryPairFrame Row9Top (Fin 6) :=
  BinaryPairFrame.ofGenerators pointChart row9Generators row9Tops row9_preserves

theorem row9_top_generator (i : Fin 3) :
    row9Frame.top (closureGenerators row9Generators i) = row9Tops i :=
  BinaryPairFrame.ofGenerators_top_generator pointChart row9Generators row9Tops row9_preserves i

theorem row9Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row9Interface.top (Fin 12)) 2 := by
  apply row9Frame.permutationFunctionRepresentation_uniform_of_coordinateTop 1
  let c := (closureGenerators row9Generators 1)⁻¹
  let b := c ^ 2 * closureGenerators row9Generators 2
  apply uniform_subgroup row9Frame.top.range
    (row9Frame.top.rangeRestrict c) (row9Frame.top.rangeRestrict b)
  · change row9Frame.top ((closureGenerators row9Generators 1)⁻¹) =
      BinarySixPointSymmetricMatrixBlocks.rotation
    rw [map_inv, row9_top_generator]
    decide +kernel
  · change row9Frame.top (((closureGenerators row9Generators 1)⁻¹) ^ 2 *
      closureGenerators row9Generators 2) = BinarySixPointSymmetricMatrixBlocks.reflection
    rw [map_mul, map_pow, map_inv, row9_top_generator, row9_top_generator]
    decide +kernel

def row103Witness : LiteralCyclicOrbitWitness Row103Top 2 where
  element := closureGenerators row103Generators 2 * closureGenerators row103Generators 0
  representative := ![0, 2]
  orbitIndex := ![0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1]
  exponent := ![0, 4, 0, 1, 1, 5, 4, 2, 2, 3, 5, 3]
  point_eq := by decide +kernel

theorem row103Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row103Interface.top (Fin 12)) 2 :=
  row103Witness.uniform _

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveOppositePairNaturalFamily

end
