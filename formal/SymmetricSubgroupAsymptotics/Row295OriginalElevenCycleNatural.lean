import SymmetricSubgroupAsymptotics.BinaryElevenCyclePolynomial
import SymmetricSubgroupAsymptotics.FiniteGeneratorWord
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows251To301
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row295OriginalElevenCycleNatural
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
def cycleWord : FiniteGeneratorWord (Fin 2) := (.mul (.generator 0) (.mul (.inv (.generator 1)) (.mul (.inv (.generator 1)) (.mul (.inv (.generator 1)) .one))))
def cycleElement : row295Interface.top := cycleWord.eval (closureGenerators row295Generators)
def pointChart : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 11, 10, 8, 2, 3, 1, 5, 9, 6, 4, 7] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 6, 4, 5, 10, 7, 9, 11, 3, 8, 2, 1] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row295Interface.top (Fin 12)) 1 := by
  apply BinaryElevenCyclePolynomial.uniform_of_basis _ cycleElement
    (closureGenerators row295Generators 0) pointChart
  decide +kernel
end SymmetricSubgroupAsymptotics.Row295OriginalElevenCycleNatural
