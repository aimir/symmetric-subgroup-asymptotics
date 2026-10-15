import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFiveCyclePairNaturalFamily

/-! A single original pair flip and a five-cycle moving its ternary
transport provide the same even-kernel and polynomial-module witnesses.
The mover need not be an involution: the five-cycle norm has the same
compressed action whenever it moves the fixed pair into the five-cycle. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFiveCycleWordNaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open PrimitiveAffineDegreeTwoTwelveFiveCyclePairNaturalFamily

def row286Tops : Fin 3 → Equiv.Perm (Fin 6) := ![1, pairThreeCycle, pairCycleB]

theorem row286Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row286Interface.top (Fin 12)) 1 := by
  let k := closureGenerators row286Generators 0
  let a := closureGenerators row286Generators 2
  let b := closureGenerators row286Generators 1
  let q := transportB a b
  apply uniform_of_words 1 row286Generators row286Tops 2 1
    (fun i ↦ k * (q i * k * (q i)⁻¹)) q k
  · unfold BinaryPairFrame.Preserves
    decide +kernel
  all_goals decide +kernel

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFiveCycleWordNaturalFamily

end
