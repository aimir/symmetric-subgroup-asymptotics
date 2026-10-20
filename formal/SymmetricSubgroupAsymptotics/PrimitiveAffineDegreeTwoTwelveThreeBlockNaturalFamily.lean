import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.PermutationNaturalBoundPointEmbedding
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250

/-!
# Seventeen natural bounds from one three-block model

A double transposition on one four-point block, together with a cyclic
permutation of three such blocks, gives a product with two six-point
orbits. Six target tuples contain the same two permutations. One fixed
point chart identifies the pair in eleven more target tuples. Every
conclusion concerns the original target top and its stored bound two.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveThreeBlockNaturalFamily

open DegreeTwoTwelvePairFiniteCatalogue

def blockGenerators : Fin 2 → Equiv.Perm (Fin 12) :=
  ![row21Generators 0, row21Generators 1]

abbrev BlockTop := Subgroup.closure (Set.range blockGenerators)

def witness : LiteralCyclicOrbitWitness BlockTop 2 where
  element := closureGenerators blockGenerators 0 * closureGenerators blockGenerators 1
  representative := ![0, 1]
  orbitIndex := ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
  exponent := ![0, 0, 2, 2, 1, 4, 3, 3, 5, 5, 4, 1]
  point_eq := by decide +kernel

theorem modelNatural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) BlockTop (Fin 12)) 2 :=
  witness.uniform _

/-- The second labelling places the local double transposition on
(0,11)(1,2), with the three-block cycle unchanged. -/
def secondChart : Fin 12 ≃ Fin 12 where
  toFun := ![3, 9, 0, 6, 7, 1, 4, 10, 11, 5, 8, 2]
  invFun := ![2, 5, 11, 0, 6, 9, 3, 4, 10, 1, 7, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def modelEmbedding {m : ℕ} (gs : Fin m → Equiv.Perm (Fin 12))
    (i j : Fin m) (e : Fin 12 ≃ Fin 12)
    (h0 : ∀ x, e (row21Generators 0 x) = gs i (e x))
    (h1 : ∀ x, e (row21Generators 1 x) = gs j (e x)) :
    LiteralPermutationGeneratorEmbedding blockGenerators
      (Subgroup.closure (Set.range gs)) where
  pointEquiv := e
  images := ![closureGenerators gs i, closureGenerators gs j]
  point_eq := by
    intro k x
    fin_cases k
    · exact h0 x
    · exact h1 x

theorem row21Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row21Interface.top (Fin 12)) 2 :=
  (modelEmbedding row21Generators 0 1 (Equiv.refl _)
    (by decide +kernel) (by decide +kernel)).uniform modelNatural

theorem row55Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row55Interface.top (Fin 12)) 2 :=
  (modelEmbedding row55Generators 0 2 (Equiv.refl _)
    (by decide +kernel) (by decide +kernel)).uniform modelNatural

theorem row56Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row56Interface.top (Fin 12)) 2 :=
  (modelEmbedding row56Generators 0 2 (Equiv.refl _)
    (by decide +kernel) (by decide +kernel)).uniform modelNatural

theorem row90Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row90Interface.top (Fin 12)) 2 :=
  (modelEmbedding row90Generators 1 2 (Equiv.refl _)
    (by decide +kernel) (by decide +kernel)).uniform modelNatural

theorem row95Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row95Interface.top (Fin 12)) 2 :=
  (modelEmbedding row95Generators 0 2 (Equiv.refl _)
    (by decide +kernel) (by decide +kernel)).uniform modelNatural

theorem row101Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row101Interface.top (Fin 12)) 2 :=
  (modelEmbedding row101Generators 0 2 (Equiv.refl _)
    (by decide +kernel) (by decide +kernel)).uniform modelNatural

theorem row57Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row57Interface.top (Fin 12)) 2 :=
  (modelEmbedding row57Generators 0 1 secondChart
    (by decide +kernel) (by decide +kernel)).uniform modelNatural

theorem row96Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row96Interface.top (Fin 12)) 2 :=
  (modelEmbedding row96Generators 0 1 secondChart
    (by decide +kernel) (by decide +kernel)).uniform modelNatural

theorem row97Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row97Interface.top (Fin 12)) 2 :=
  (modelEmbedding row97Generators 0 1 secondChart
    (by decide +kernel) (by decide +kernel)).uniform modelNatural

theorem row100Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row100Interface.top (Fin 12)) 2 :=
  (modelEmbedding row100Generators 0 1 secondChart
    (by decide +kernel) (by decide +kernel)).uniform modelNatural

theorem row106Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row106Interface.top (Fin 12)) 2 :=
  (modelEmbedding row106Generators 0 3 secondChart
    (by decide +kernel) (by decide +kernel)).uniform modelNatural

theorem row144Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row144Interface.top (Fin 12)) 2 :=
  (modelEmbedding row144Generators 0 2 secondChart
    (by decide +kernel) (by decide +kernel)).uniform modelNatural

theorem row184Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row184Interface.top (Fin 12)) 2 :=
  (modelEmbedding row184Generators 0 2 secondChart
    (by decide +kernel) (by decide +kernel)).uniform modelNatural

theorem row187Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row187Interface.top (Fin 12)) 2 :=
  (modelEmbedding row187Generators 0 2 secondChart
    (by decide +kernel) (by decide +kernel)).uniform modelNatural

theorem row190Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row190Interface.top (Fin 12)) 2 :=
  (modelEmbedding row190Generators 0 2 secondChart
    (by decide +kernel) (by decide +kernel)).uniform modelNatural

theorem row191Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row191Interface.top (Fin 12)) 2 :=
  (modelEmbedding row191Generators 0 2 secondChart
    (by decide +kernel) (by decide +kernel)).uniform modelNatural

theorem row226Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row226Interface.top (Fin 12)) 2 :=
  (modelEmbedding row226Generators 0 2 secondChart
    (by decide +kernel) (by decide +kernel)).uniform modelNatural

end DegreeTwoTwelveThreeBlockNaturalFamily
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
