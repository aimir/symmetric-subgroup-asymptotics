import SymmetricSubgroupAsymptotics.BinaryTwoTernaryPairOperator
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFullPairKernelNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50

/-! Five capacity-two fields from one cyclic six-point pair module.
The literal pair-sum exact sequence supplies the original twelve-point
bound. No independent-flip hypothesis is needed for these five rows. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveTwoTernaryPairNaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

abbrev pointChart := PrimitiveAffineDegreeTwoTwelveFullPairKernelNaturalFamily.pointChart

def reflection : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 4, 3, 2, 1]
  invFun := ![0, 5, 4, 3, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def oddRotation : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 2, 5, 4, 1]
  invFun := ![0, 5, 2, 1, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def frame {m : ℕ} (gs : Fin m → Equiv.Perm (Fin 12))
    (tops : Fin m → Equiv.Perm (Fin 6))
    (hp : ∀ i, BinaryPairFrame.Preserves pointChart (gs i) (tops i)) :
    BinaryPairFrame (Subgroup.closure (Set.range gs)) (Fin 6) :=
  BinaryPairFrame.ofGenerators pointChart gs tops hp

theorem pair_uniform {m : ℕ} (j : Fin 3)
    (gs : Fin m → Equiv.Perm (Fin 12)) (tops : Fin m → Equiv.Perm (Fin 6))
    (ti ci : Fin m)
    (hp : ∀ i, BinaryPairFrame.Preserves pointChart (gs i) (tops i))
    (ht : tops ti = BinaryTwoTernaryPairOperator.rotation)
    (hc : tops ci = BinaryTwoTernaryPairOperator.mover j) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) (frame gs tops hp).top.range (Fin 6)) 1 := by
  apply BinaryTwoTernaryPairOperator.uniform_subgroup j _
    ((frame gs tops hp).top.rangeRestrict (closureGenerators gs ti))
    ((frame gs tops hp).top.rangeRestrict (closureGenerators gs ci))
  · exact (BinaryPairFrame.ofGenerators_top_generator pointChart gs tops hp ti).trans ht
  · exact (BinaryPairFrame.ofGenerators_top_generator pointChart gs tops hp ci).trans hc

theorem uniform_two {m : ℕ} (j : Fin 3)
    (gs : Fin m → Equiv.Perm (Fin 12)) (tops : Fin m → Equiv.Perm (Fin 6))
    (ti ci : Fin m)
    (hp : ∀ i, BinaryPairFrame.Preserves pointChart (gs i) (tops i))
    (ht : tops ti = BinaryTwoTernaryPairOperator.rotation)
    (hc : tops ci = BinaryTwoTernaryPairOperator.mover j) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2)
        (Subgroup.closure (Set.range gs)) (Fin 12)) 2 :=
  (frame gs tops hp).permutationFunctionRepresentation_uniform_of_coordinateTop 1
    (pair_uniform j gs tops ti ci hp ht hc)

open BinaryTwoTernaryPairOperator in
def row40Tops : Fin 4 → Equiv.Perm (Fin 6) := ![rotation, reflection, mover 0, 1]

open BinaryTwoTernaryPairOperator in
def row158Tops : Fin 3 → Equiv.Perm (Fin 6) := ![1, rotation, mover 1]

open BinaryTwoTernaryPairOperator in
def row162Tops : Fin 5 → Equiv.Perm (Fin 6) := ![1, 1, rotation, reflection, mover 0]

open BinaryTwoTernaryPairOperator in
def row163Tops : Fin 5 → Equiv.Perm (Fin 6) := ![1, 1, rotation, reflection, mover 1]

open BinaryTwoTernaryPairOperator in
def row199Tops : Fin 4 → Equiv.Perm (Fin 6) := ![1, rotation, reflection, mover 0]

theorem row40Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row40Interface.top (Fin 12)) 2 := by
  apply uniform_two 0 row40Generators row40Tops 0 2
  · unfold BinaryPairFrame.Preserves
    decide +kernel
  all_goals decide +kernel

theorem row158Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row158Interface.top (Fin 12)) 2 := by
  apply uniform_two 1 row158Generators row158Tops 1 2
  · unfold BinaryPairFrame.Preserves
    decide +kernel
  all_goals decide +kernel

theorem row162Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row162Interface.top (Fin 12)) 2 := by
  apply uniform_two 0 row162Generators row162Tops 2 4
  · unfold BinaryPairFrame.Preserves
    decide +kernel
  all_goals decide +kernel

theorem row163Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row163Interface.top (Fin 12)) 2 := by
  apply uniform_two 1 row163Generators row163Tops 2 4
  · unfold BinaryPairFrame.Preserves
    decide +kernel
  all_goals decide +kernel

theorem row199Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row199Interface.top (Fin 12)) 2 := by
  apply uniform_two 0 row199Generators row199Tops 1 3
  · unfold BinaryPairFrame.Preserves
    decide +kernel
  all_goals decide +kernel

end PrimitiveAffineDegreeTwoTwelveTwoTernaryPairNaturalFamily
end SymmetricSubgroupAsymptotics

end
