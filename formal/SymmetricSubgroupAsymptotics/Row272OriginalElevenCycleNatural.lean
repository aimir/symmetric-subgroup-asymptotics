import SymmetricSubgroupAsymptotics.BinaryElevenCyclePolynomial
import SymmetricSubgroupAsymptotics.FiniteGeneratorWord
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows251To301
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row272OriginalElevenCycleNatural
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
def cycleWord : FiniteGeneratorWord (Fin 2) := (.mul (.generator 0) (.mul (.generator 0) (.mul (.inv (.generator 1)) .one)))
def cycleElement : row272Interface.top := cycleWord.eval (closureGenerators row272Generators)
def pointChart : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 11, 9, 6, 7, 3, 8, 4, 10, 5, 2, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 11, 10, 5, 7, 9, 3, 4, 6, 2, 8, 1] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row272Interface.top (Fin 12)) 1 := by
  apply BinaryElevenCyclePolynomial.uniform_of_basis _ cycleElement
    (closureGenerators row272Generators 0) pointChart
  decide +kernel
end SymmetricSubgroupAsymptotics.Row272OriginalElevenCycleNatural
