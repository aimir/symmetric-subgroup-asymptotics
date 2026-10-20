import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveCentralInvolutionNaturalFamily

/-! A ternary norm of a cross-half double flip produces the global pair
flip. Its product with the ternary shift has the same two six-point
cycles in six original actions. One field is at its stored cap two; five
are explicitly weaker cap-two bounds for a flexible capacity package.
The original row27 action also inherits cap two from the row6 subtuple. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlipNormNaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def normWord {G : Type} [Group G] (k c : G) : G :=
  c * (k * (c * k * c⁻¹) * (c ^ 2 * k * (c ^ 2)⁻¹))

def normWitness {H : Subgroup (Equiv.Perm (Fin 12))} (k c : H)
    (h : ((normWord k c : H) : Equiv.Perm (Fin 12)) =
      PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily.row3Witness.element.val) :
    LiteralCyclicOrbitWitness H 2 where
  element := normWord k c
  representative := PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily.row3Witness.representative
  orbitIndex := PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily.row3Witness.orbitIndex
  exponent := PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily.row3Witness.exponent
  point_eq x := by
    rw [h]
    exact PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily.row3Witness.point_eq x

theorem row54NaturalTwo : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row54Interface.top (Fin 12)) 2 :=
  (normWitness (closureGenerators row54Generators 0)
    (closureGenerators row54Generators 1) (by decide +kernel)).uniform _

theorem row88Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row88Interface.top (Fin 12)) 2 :=
  (normWitness (closureGenerators row88Generators 0)
    (closureGenerators row88Generators 2) (by decide +kernel)).uniform _

theorem row146NaturalTwo : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row146Interface.top (Fin 12)) 2 :=
  (normWitness (closureGenerators row146Generators 0)
    (closureGenerators row146Generators 3) (by decide +kernel)).uniform _

theorem row149NaturalTwo : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row149Interface.top (Fin 12)) 2 :=
  (normWitness (closureGenerators row149Generators 0)
    (closureGenerators row149Generators 2) (by decide +kernel)).uniform _

theorem row154NaturalTwo : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row154Interface.top (Fin 12)) 2 :=
  (normWitness (closureGenerators row154Generators 0)
    (closureGenerators row154Generators 1) (by decide +kernel)).uniform _

theorem row155NaturalTwo : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row155Interface.top (Fin 12)) 2 :=
  (normWitness (closureGenerators row155Generators 0)
    (closureGenerators row155Generators 1) (by decide +kernel)).uniform _

def row27Embedding : LiteralPermutationGeneratorEmbedding row6Generators Row27Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row27Generators 1, closureGenerators row27Generators 2,
    closureGenerators row27Generators 0]
  point_eq := by decide +kernel

theorem row27NaturalTwo : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row27Interface.top (Fin 12)) 2 :=
  row27Embedding.uniform PrimitiveAffineDegreeTwoTwelveCentralInvolutionNaturalFamily.row6Natural

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlipNormNaturalFamily

end
