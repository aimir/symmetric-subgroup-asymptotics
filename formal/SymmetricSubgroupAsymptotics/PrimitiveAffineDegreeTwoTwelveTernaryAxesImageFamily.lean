import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTernaryAxesImagePilot
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250

/-! Three more original actions have scalar-and-swap ternary pair images.
Literal sum/difference codes bind every original generator to the shared
actual image. No full-image equality or splitting is assumed. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTernaryAxesImageFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue SixPointTernaryAxesNormalGenerators

def row196Codes : Fin 4 → Model := ![(1, 1), (translation, translation), (translation, translation * reflection), (reflection, reflection)]

def row196Tops (i : Fin 4) : Equiv.Perm (Fin 6) := literalAction (row196Codes i)

theorem row196_preserves : ∀ i,
    BinaryPairFrame.Preserves SixPairCyclicSymmetricSocles.pointChart
      (row196Generators i) (row196Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def row196Frame : BinaryPairFrame Row196Top (Fin 6) :=
  BinaryPairFrame.ofGenerators SixPairCyclicSymmetricSocles.pointChart
    row196Generators row196Tops row196_preserves

theorem row196_range_le : row196Frame.top.range ≤ literalAction.range := by
  change (BinaryPairFrame.ofGenerators SixPairCyclicSymmetricSocles.pointChart
    row196Generators row196Tops row196_preserves).top.range ≤ literalAction.range
  rw [BinaryPairFrame.ofGenerators_top_range]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  exact ⟨row196Codes i,rfl⟩

theorem row196AtThree_quotientSocle
    (huniform : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) Row196Top (Fin 12)) 1)
    (N : Subgroup Row196Top) [N.Normal] : SocleNormalGeneratorBound (Row196Top ⧸ N) 3 :=
  quotientSocle_of_original_natural row196Frame row196_range_le huniform N

def row196AtThree_family
    (huniform : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) Row196Top (Fin 12)) 1) :
    row196Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row196AtThree_quotientSocle huniform N.1)

def row197Codes : Fin 4 → Model := ![(1, 1), (translation, translation), (translation ^ 2 * reflection, translation * reflection), (1, translation * reflection)]

def row197Tops (i : Fin 4) : Equiv.Perm (Fin 6) := literalAction (row197Codes i)

theorem row197_preserves : ∀ i,
    BinaryPairFrame.Preserves SixPairCyclicSymmetricSocles.pointChart
      (row197Generators i) (row197Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def row197Frame : BinaryPairFrame Row197Top (Fin 6) :=
  BinaryPairFrame.ofGenerators SixPairCyclicSymmetricSocles.pointChart
    row197Generators row197Tops row197_preserves

theorem row197_range_le : row197Frame.top.range ≤ literalAction.range := by
  change (BinaryPairFrame.ofGenerators SixPairCyclicSymmetricSocles.pointChart
    row197Generators row197Tops row197_preserves).top.range ≤ literalAction.range
  rw [BinaryPairFrame.ofGenerators_top_range]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  exact ⟨row197Codes i,rfl⟩

theorem row197AtThree_quotientSocle
    (huniform : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) Row197Top (Fin 12)) 1)
    (N : Subgroup Row197Top) [N.Normal] : SocleNormalGeneratorBound (Row197Top ⧸ N) 3 :=
  quotientSocle_of_original_natural row197Frame row197_range_le huniform N

def row197AtThree_family
    (huniform : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) Row197Top (Fin 12)) 1) :
    row197Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row197AtThree_quotientSocle huniform N.1)

def row240Codes : Fin 4 → Model := ![(1, 1), (translation, translation), (translation ^ 2 * reflection, translation * reflection), (1, translation * reflection)]

def row240Tops (i : Fin 4) : Equiv.Perm (Fin 6) := literalAction (row240Codes i)

theorem row240_preserves : ∀ i,
    BinaryPairFrame.Preserves SixPairCyclicSymmetricSocles.pointChart
      (row240Generators i) (row240Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def row240Frame : BinaryPairFrame Row240Top (Fin 6) :=
  BinaryPairFrame.ofGenerators SixPairCyclicSymmetricSocles.pointChart
    row240Generators row240Tops row240_preserves

theorem row240_range_le : row240Frame.top.range ≤ literalAction.range := by
  change (BinaryPairFrame.ofGenerators SixPairCyclicSymmetricSocles.pointChart
    row240Generators row240Tops row240_preserves).top.range ≤ literalAction.range
  rw [BinaryPairFrame.ofGenerators_top_range]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  exact ⟨row240Codes i,rfl⟩

theorem row240AtThree_quotientSocle
    (huniform : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) Row240Top (Fin 12)) 1)
    (N : Subgroup Row240Top) [N.Normal] : SocleNormalGeneratorBound (Row240Top ⧸ N) 3 :=
  quotientSocle_of_original_natural row240Frame row240_range_le huniform N

def row240AtThree_family
    (huniform : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) Row240Top (Fin 12)) 1) :
    row240Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row240AtThree_quotientSocle huniform N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTernaryAxesImageFamily

end
