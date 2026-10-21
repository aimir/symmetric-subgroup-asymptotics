import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePrimitiveFinalPublishedSocles
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixActualNormalConsumers
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.SixPairPrimitiveFinalPublishedSoclesDirectConsumers

/-! Isolated direct six-point and coarse twelve-point consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

noncomputable section

open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePrimitiveFinalPublishedSocles

namespace DirectConsumers

open Non2UnipotentPrefixFiniteMenu

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

open DegreeTwoTwelvePairFiniteCatalogue BinarySixPointFiveCyclePolynomial

theorem row33AtTwo_quotientSocle (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (N : Subgroup Row33Top) [N.Normal] : SocleNormalGeneratorBound (Row33Top ⧸ N) 2 :=
  _root_.SymmetricSubgroupAsymptotics.SixPairPrimitiveFinalPublishedSocles.DirectConsumers.quotientSocle_of_generators socle catalogue
    SixPairCyclicSymmetricSocles.pointChart row33Generators row33Tops 0 1 row33_preserves
    (by decide +kernel) (by decide +kernel) row33_matrix N

def row33AtTwo_family (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    row33Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact _root_.SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePrimitiveFinalPublishedSocles.DirectConsumers.row33AtTwo_quotientSocle socle catalogue N.1)

theorem row75AtTwo_quotientSocle (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (N : Subgroup Row75Top) [N.Normal] : SocleNormalGeneratorBound (Row75Top ⧸ N) 2 :=
  _root_.SymmetricSubgroupAsymptotics.SixPairPrimitiveFinalPublishedSocles.DirectConsumers.quotientSocle_of_generators socle catalogue
    SixPairCyclicSymmetricSocles.pointChart row75Generators row75Tops 0 1 row75_preserves
    (by decide +kernel) (by decide +kernel) row75_matrix N

def row75AtTwo_family (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    row75Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact _root_.SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePrimitiveFinalPublishedSocles.DirectConsumers.row75AtTwo_quotientSocle socle catalogue N.1)

theorem row76AtTwo_quotientSocle (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (N : Subgroup Row76Top) [N.Normal] : SocleNormalGeneratorBound (Row76Top ⧸ N) 2 :=
  _root_.SymmetricSubgroupAsymptotics.SixPairPrimitiveFinalPublishedSocles.DirectConsumers.quotientSocle_of_generators socle catalogue
    shiftedFrame row76Generators row76Tops 1 3 row76_preserves
    (by decide +kernel) (by decide +kernel) row76_matrix N

def row76AtTwo_family (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    row76Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact _root_.SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePrimitiveFinalPublishedSocles.DirectConsumers.row76AtTwo_quotientSocle socle catalogue N.1)

theorem row123AtTwo_quotientSocle (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (N : Subgroup Row123Top) [N.Normal] : SocleNormalGeneratorBound (Row123Top ⧸ N) 2 :=
  _root_.SymmetricSubgroupAsymptotics.SixPairPrimitiveFinalPublishedSocles.DirectConsumers.quotientSocle_of_generators socle catalogue
    SixPairCyclicSymmetricSocles.pointChart row123Generators row123Tops 0 1 row123_preserves
    (by decide +kernel) (by decide +kernel) row123_matrix N

def row123AtTwo_family (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    row123Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact _root_.SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePrimitiveFinalPublishedSocles.DirectConsumers.row123AtTwo_quotientSocle socle catalogue N.1)

theorem row124AtTwo_quotientSocle (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (N : Subgroup Row124Top) [N.Normal] : SocleNormalGeneratorBound (Row124Top ⧸ N) 2 :=
  _root_.SymmetricSubgroupAsymptotics.SixPairPrimitiveFinalPublishedSocles.DirectConsumers.quotientSocle_of_generators socle catalogue
    shiftedFrame row124Generators row124Tops 1 2 row124_preserves
    (by decide +kernel) (by decide +kernel) row124_matrix N

def row124AtTwo_family (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    row124Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact _root_.SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePrimitiveFinalPublishedSocles.DirectConsumers.row124AtTwo_quotientSocle socle catalogue N.1)

theorem row180AtTwo_quotientSocle (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (N : Subgroup Row180Top) [N.Normal] : SocleNormalGeneratorBound (Row180Top ⧸ N) 2 :=
  _root_.SymmetricSubgroupAsymptotics.SixPairPrimitiveFinalPublishedSocles.DirectConsumers.quotientSocle_of_generators socle catalogue
    shiftedFrame row180Generators row180Tops 1 0 row180_preserves
    (by decide +kernel) (by decide +kernel) row180_matrix N

def row180AtTwo_family (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    row180Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact _root_.SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePrimitiveFinalPublishedSocles.DirectConsumers.row180AtTwo_quotientSocle socle catalogue N.1)

theorem row183AtTwo_quotientSocle (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (N : Subgroup Row183Top) [N.Normal] : SocleNormalGeneratorBound (Row183Top ⧸ N) 2 :=
  _root_.SymmetricSubgroupAsymptotics.SixPairPrimitiveFinalPublishedSocles.DirectConsumers.quotientSocle_of_generators socle catalogue
    shiftedFrame row183Generators row183Tops 1 0 row183_preserves
    (by decide +kernel) (by decide +kernel) row183_matrix N

def row183AtTwo_family (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    row183Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact _root_.SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePrimitiveFinalPublishedSocles.DirectConsumers.row183AtTwo_quotientSocle socle catalogue N.1)

theorem row230AtTwo_quotientSocle (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (N : Subgroup Row230Top) [N.Normal] : SocleNormalGeneratorBound (Row230Top ⧸ N) 2 :=
  _root_.SymmetricSubgroupAsymptotics.SixPairPrimitiveFinalPublishedSocles.DirectConsumers.quotientSocle_of_generators socle catalogue
    SixPairCyclicSymmetricSocles.pointChart row230Generators row230Tops 1 2 row230_preserves
    (by decide +kernel) (by decide +kernel) row230_matrix N

def row230AtTwo_family (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    row230Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact _root_.SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePrimitiveFinalPublishedSocles.DirectConsumers.row230AtTwo_quotientSocle socle catalogue N.1)

theorem row255AtTwo_quotientSocle (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (N : Subgroup Row255Top) [N.Normal] : SocleNormalGeneratorBound (Row255Top ⧸ N) 2 :=
  _root_.SymmetricSubgroupAsymptotics.SixPairPrimitiveFinalPublishedSocles.DirectConsumers.quotientSocle_of_generators socle catalogue
    SixPairCyclicSymmetricSocles.pointChart row255Generators row255Tops 1 2 row255_preserves
    (by decide +kernel) (by decide +kernel) row255_matrix N

def row255AtTwo_family (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    row255Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact _root_.SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePrimitiveFinalPublishedSocles.DirectConsumers.row255AtTwo_quotientSocle socle catalogue N.1)

theorem row256AtTwo_quotientSocle (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (N : Subgroup Row256Top) [N.Normal] : SocleNormalGeneratorBound (Row256Top ⧸ N) 2 :=
  _root_.SymmetricSubgroupAsymptotics.SixPairPrimitiveFinalPublishedSocles.DirectConsumers.quotientSocle_of_generators socle catalogue
    SixPairCyclicSymmetricSocles.pointChart row256Generators row256Tops 1 2 row256_preserves
    (by decide +kernel) (by decide +kernel) row256_matrix N

def row256AtTwo_family (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    row256Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact _root_.SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePrimitiveFinalPublishedSocles.DirectConsumers.row256AtTwo_quotientSocle socle catalogue N.1)

theorem row257AtTwo_quotientSocle (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (N : Subgroup Row257Top) [N.Normal] : SocleNormalGeneratorBound (Row257Top ⧸ N) 2 :=
  _root_.SymmetricSubgroupAsymptotics.SixPairPrimitiveFinalPublishedSocles.DirectConsumers.quotientSocle_of_generators socle catalogue
    SixPairCyclicSymmetricSocles.pointChart row257Generators row257Tops 1 2 row257_preserves
    (by decide +kernel) (by decide +kernel) row257_matrix N

def row257AtTwo_family (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    row257Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact _root_.SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePrimitiveFinalPublishedSocles.DirectConsumers.row257AtTwo_quotientSocle socle catalogue N.1)

theorem row270AtTwo_quotientSocle (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (N : Subgroup Row270Top) [N.Normal] : SocleNormalGeneratorBound (Row270Top ⧸ N) 2 :=
  _root_.SymmetricSubgroupAsymptotics.SixPairPrimitiveFinalPublishedSocles.DirectConsumers.quotientSocle_of_generators socle catalogue
    SixPairCyclicSymmetricSocles.pointChart row270Generators row270Tops 1 2 row270_preserves
    (by decide +kernel) (by decide +kernel) row270_matrix N

def row270AtTwo_family (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    row270Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact _root_.SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePrimitiveFinalPublishedSocles.DirectConsumers.row270AtTwo_quotientSocle socle catalogue N.1)

theorem row277AtTwo_quotientSocle (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (N : Subgroup Row277Top) [N.Normal] : SocleNormalGeneratorBound (Row277Top ⧸ N) 2 :=
  _root_.SymmetricSubgroupAsymptotics.SixPairPrimitiveFinalPublishedSocles.DirectConsumers.quotientSocle_of_generators socle catalogue
    shiftedFrame row277Generators row277Tops 2 1 row277_preserves
    (by decide +kernel) (by decide +kernel) row277_matrix N

def row277AtTwo_family (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    row277Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact _root_.SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePrimitiveFinalPublishedSocles.DirectConsumers.row277AtTwo_quotientSocle socle catalogue N.1)

theorem row286AtTwo_quotientSocle (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (N : Subgroup Row286Top) [N.Normal] : SocleNormalGeneratorBound (Row286Top ⧸ N) 2 :=
  _root_.SymmetricSubgroupAsymptotics.SixPairPrimitiveFinalPublishedSocles.DirectConsumers.quotientSocle_of_generators socle catalogue
    shiftedFrame row286Generators row286Tops 2 1 row286_preserves
    (by decide +kernel) (by decide +kernel) row286_matrix N

def row286AtTwo_family (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    row286Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact _root_.SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePrimitiveFinalPublishedSocles.DirectConsumers.row286AtTwo_quotientSocle socle catalogue N.1)

theorem row287AtTwo_quotientSocle (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (N : Subgroup Row287Top) [N.Normal] : SocleNormalGeneratorBound (Row287Top ⧸ N) 2 :=
  _root_.SymmetricSubgroupAsymptotics.SixPairPrimitiveFinalPublishedSocles.DirectConsumers.quotientSocle_of_generators socle catalogue
    shiftedFrame row287Generators row287Tops 2 1 row287_preserves
    (by decide +kernel) (by decide +kernel) row287_matrix N

def row287AtTwo_family (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    row287Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact _root_.SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePrimitiveFinalPublishedSocles.DirectConsumers.row287AtTwo_quotientSocle socle catalogue N.1)

end DirectConsumers

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePrimitiveFinalPublishedSocles

end

