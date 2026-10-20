import SymmetricSubgroupAsymptotics.SixPairPrimitiveFinalPublishedSocles
import SymmetricSubgroupAsymptotics.SixPairCyclicSymmetricSocles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows251To301

/-! Fifteen actual primitive six-pair images use the two published inputs
already present in final T1. Their original generators, point actions,
normal quotients and natural-module capacities are retained. These are
parameterized proved packages; no separate degree-six classification or
project rank assertion is supplied. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePrimitiveFinalPublishedSocles

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue BinarySixPointFiveCyclePolynomial

def shiftedFrame : Fin 6 × ZMod 2 ≃ Fin 12 where
  toFun p := if p.2 = 0 then ![1,3,5,7,9,0] p.1 else ![2,4,6,8,10,11] p.1
  invFun x := (![5,0,0,1,1,2,2,3,3,4,4,5] x,
    ![0,0,1,0,1,0,1,0,1,0,1,1] x)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row33Tops (i : Fin 2) : Equiv.Perm (Fin 6) where
  toFun := (![![1, 2, 3, 4, 0, 5], ![5, 3, 0, 4, 1, 2]] : Fin 2 → Fin 6 → Fin 6) i
  invFun := (![![4, 0, 1, 2, 3, 5], ![2, 4, 5, 1, 3, 0]] : Fin 2 → Fin 6 → Fin 6) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

theorem row33_preserves : ∀ i,
    BinaryPairFrame.Preserves SixPairCyclicSymmetricSocles.pointChart (row33Generators i) (row33Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row33_matrix : ∀ i x : Fin 6,
    actualOperator representation SixPointFiveCyclePrimitive.cycle (row33Tops 1) (Pi.single i 1) x =
      operator 0 (Pi.single i 1) x := by
  decide +kernel

theorem row33AtTwo_quotientSocle (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (N : Subgroup Row33Top) [N.Normal] : SocleNormalGeneratorBound (Row33Top ⧸ N) 2 :=
  SixPairPrimitiveFinalPublishedSocles.quotientSocle_of_generators socle catalogue
    SixPairCyclicSymmetricSocles.pointChart row33Generators row33Tops 0 1 row33_preserves
    (by decide +kernel) (by decide +kernel) row33_matrix N

def row33AtTwo_family (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    row33Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row33AtTwo_quotientSocle socle catalogue N.1)

def row75Tops (i : Fin 3) : Equiv.Perm (Fin 6) where
  toFun := (![![1, 2, 3, 4, 0, 5], ![5, 4, 2, 3, 1, 0], ![0, 1, 2, 3, 4, 5]] : Fin 3 → Fin 6 → Fin 6) i
  invFun := (![![4, 0, 1, 2, 3, 5], ![5, 4, 2, 3, 1, 0], ![0, 1, 2, 3, 4, 5]] : Fin 3 → Fin 6 → Fin 6) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

theorem row75_preserves : ∀ i,
    BinaryPairFrame.Preserves SixPairCyclicSymmetricSocles.pointChart (row75Generators i) (row75Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row75_matrix : ∀ i x : Fin 6,
    actualOperator representation SixPointFiveCyclePrimitive.cycle (row75Tops 1) (Pi.single i 1) x =
      operator 0 (Pi.single i 1) x := by
  decide +kernel

theorem row75AtTwo_quotientSocle (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (N : Subgroup Row75Top) [N.Normal] : SocleNormalGeneratorBound (Row75Top ⧸ N) 2 :=
  SixPairPrimitiveFinalPublishedSocles.quotientSocle_of_generators socle catalogue
    SixPairCyclicSymmetricSocles.pointChart row75Generators row75Tops 0 1 row75_preserves
    (by decide +kernel) (by decide +kernel) row75_matrix N

def row75AtTwo_family (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    row75Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row75AtTwo_quotientSocle socle catalogue N.1)

def row76Tops (i : Fin 4) : Equiv.Perm (Fin 6) where
  toFun := (![![0, 1, 2, 3, 4, 5], ![1, 2, 3, 4, 0, 5], ![0, 4, 3, 2, 1, 5], ![5, 4, 2, 3, 1, 0]] : Fin 4 → Fin 6 → Fin 6) i
  invFun := (![![0, 1, 2, 3, 4, 5], ![4, 0, 1, 2, 3, 5], ![0, 4, 3, 2, 1, 5], ![5, 4, 2, 3, 1, 0]] : Fin 4 → Fin 6 → Fin 6) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

theorem row76_preserves : ∀ i,
    BinaryPairFrame.Preserves shiftedFrame (row76Generators i) (row76Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row76_matrix : ∀ i x : Fin 6,
    actualOperator representation SixPointFiveCyclePrimitive.cycle (row76Tops 3) (Pi.single i 1) x =
      operator 0 (Pi.single i 1) x := by
  decide +kernel

theorem row76AtTwo_quotientSocle (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (N : Subgroup Row76Top) [N.Normal] : SocleNormalGeneratorBound (Row76Top ⧸ N) 2 :=
  SixPairPrimitiveFinalPublishedSocles.quotientSocle_of_generators socle catalogue
    shiftedFrame row76Generators row76Tops 1 3 row76_preserves
    (by decide +kernel) (by decide +kernel) row76_matrix N

def row76AtTwo_family (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    row76Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row76AtTwo_quotientSocle socle catalogue N.1)

def row123Tops (i : Fin 3) : Equiv.Perm (Fin 6) where
  toFun := (![![1, 2, 3, 4, 0, 5], ![5, 2, 1, 4, 3, 0], ![0, 1, 2, 3, 4, 5]] : Fin 3 → Fin 6 → Fin 6) i
  invFun := (![![4, 0, 1, 2, 3, 5], ![5, 2, 1, 4, 3, 0], ![0, 1, 2, 3, 4, 5]] : Fin 3 → Fin 6 → Fin 6) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

theorem row123_preserves : ∀ i,
    BinaryPairFrame.Preserves SixPairCyclicSymmetricSocles.pointChart (row123Generators i) (row123Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row123_matrix : ∀ i x : Fin 6,
    actualOperator representation SixPointFiveCyclePrimitive.cycle (row123Tops 1) (Pi.single i 1) x =
      operator 0 (Pi.single i 1) x := by
  decide +kernel

theorem row123AtTwo_quotientSocle (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (N : Subgroup Row123Top) [N.Normal] : SocleNormalGeneratorBound (Row123Top ⧸ N) 2 :=
  SixPairPrimitiveFinalPublishedSocles.quotientSocle_of_generators socle catalogue
    SixPairCyclicSymmetricSocles.pointChart row123Generators row123Tops 0 1 row123_preserves
    (by decide +kernel) (by decide +kernel) row123_matrix N

def row123AtTwo_family (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    row123Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row123AtTwo_quotientSocle socle catalogue N.1)

def row124Tops (i : Fin 3) : Equiv.Perm (Fin 6) where
  toFun := (![![0, 1, 2, 3, 4, 5], ![1, 2, 3, 4, 0, 5], ![5, 2, 1, 4, 3, 0]] : Fin 3 → Fin 6 → Fin 6) i
  invFun := (![![0, 1, 2, 3, 4, 5], ![4, 0, 1, 2, 3, 5], ![5, 2, 1, 4, 3, 0]] : Fin 3 → Fin 6 → Fin 6) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

theorem row124_preserves : ∀ i,
    BinaryPairFrame.Preserves shiftedFrame (row124Generators i) (row124Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row124_matrix : ∀ i x : Fin 6,
    actualOperator representation SixPointFiveCyclePrimitive.cycle (row124Tops 2) (Pi.single i 1) x =
      operator 0 (Pi.single i 1) x := by
  decide +kernel

theorem row124AtTwo_quotientSocle (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (N : Subgroup Row124Top) [N.Normal] : SocleNormalGeneratorBound (Row124Top ⧸ N) 2 :=
  SixPairPrimitiveFinalPublishedSocles.quotientSocle_of_generators socle catalogue
    shiftedFrame row124Generators row124Tops 1 2 row124_preserves
    (by decide +kernel) (by decide +kernel) row124_matrix N

def row124AtTwo_family (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    row124Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row124AtTwo_quotientSocle socle catalogue N.1)

def row180Tops (i : Fin 3) : Equiv.Perm (Fin 6) where
  toFun := (![![1, 5, 2, 3, 4, 0], ![1, 2, 3, 4, 0, 5], ![0, 1, 2, 3, 4, 5]] : Fin 3 → Fin 6 → Fin 6) i
  invFun := (![![5, 0, 2, 3, 4, 1], ![4, 0, 1, 2, 3, 5], ![0, 1, 2, 3, 4, 5]] : Fin 3 → Fin 6 → Fin 6) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

theorem row180_preserves : ∀ i,
    BinaryPairFrame.Preserves shiftedFrame (row180Generators i) (row180Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row180_matrix : ∀ i x : Fin 6,
    actualOperator representation SixPointFiveCyclePrimitive.cycle (row180Tops 0) (Pi.single i 1) x =
      operator 0 (Pi.single i 1) x := by
  decide +kernel

theorem row180AtTwo_quotientSocle (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (N : Subgroup Row180Top) [N.Normal] : SocleNormalGeneratorBound (Row180Top ⧸ N) 2 :=
  SixPairPrimitiveFinalPublishedSocles.quotientSocle_of_generators socle catalogue
    shiftedFrame row180Generators row180Tops 1 0 row180_preserves
    (by decide +kernel) (by decide +kernel) row180_matrix N

def row180AtTwo_family (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    row180Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row180AtTwo_quotientSocle socle catalogue N.1)

def row183Tops (i : Fin 3) : Equiv.Perm (Fin 6) where
  toFun := (![![1, 5, 2, 3, 4, 0], ![1, 2, 3, 4, 0, 5], ![0, 1, 2, 4, 3, 5]] : Fin 3 → Fin 6 → Fin 6) i
  invFun := (![![5, 0, 2, 3, 4, 1], ![4, 0, 1, 2, 3, 5], ![0, 1, 2, 4, 3, 5]] : Fin 3 → Fin 6 → Fin 6) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

theorem row183_preserves : ∀ i,
    BinaryPairFrame.Preserves shiftedFrame (row183Generators i) (row183Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row183_matrix : ∀ i x : Fin 6,
    actualOperator representation SixPointFiveCyclePrimitive.cycle (row183Tops 0) (Pi.single i 1) x =
      operator 0 (Pi.single i 1) x := by
  decide +kernel

theorem row183AtTwo_quotientSocle (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (N : Subgroup Row183Top) [N.Normal] : SocleNormalGeneratorBound (Row183Top ⧸ N) 2 :=
  SixPairPrimitiveFinalPublishedSocles.quotientSocle_of_generators socle catalogue
    shiftedFrame row183Generators row183Tops 1 0 row183_preserves
    (by decide +kernel) (by decide +kernel) row183_matrix N

def row183AtTwo_family (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    row183Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row183AtTwo_quotientSocle socle catalogue N.1)

def row230Tops (i : Fin 3) : Equiv.Perm (Fin 6) where
  toFun := (![![0, 1, 2, 3, 4, 5], ![1, 2, 3, 4, 0, 5], ![5, 4, 2, 3, 1, 0]] : Fin 3 → Fin 6 → Fin 6) i
  invFun := (![![0, 1, 2, 3, 4, 5], ![4, 0, 1, 2, 3, 5], ![5, 4, 2, 3, 1, 0]] : Fin 3 → Fin 6 → Fin 6) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

theorem row230_preserves : ∀ i,
    BinaryPairFrame.Preserves SixPairCyclicSymmetricSocles.pointChart (row230Generators i) (row230Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row230_matrix : ∀ i x : Fin 6,
    actualOperator representation SixPointFiveCyclePrimitive.cycle (row230Tops 2) (Pi.single i 1) x =
      operator 0 (Pi.single i 1) x := by
  decide +kernel

theorem row230AtTwo_quotientSocle (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (N : Subgroup Row230Top) [N.Normal] : SocleNormalGeneratorBound (Row230Top ⧸ N) 2 :=
  SixPairPrimitiveFinalPublishedSocles.quotientSocle_of_generators socle catalogue
    SixPairCyclicSymmetricSocles.pointChart row230Generators row230Tops 1 2 row230_preserves
    (by decide +kernel) (by decide +kernel) row230_matrix N

def row230AtTwo_family (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    row230Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row230AtTwo_quotientSocle socle catalogue N.1)

def row255Tops (i : Fin 3) : Equiv.Perm (Fin 6) where
  toFun := (![![0, 1, 2, 3, 4, 5], ![1, 2, 3, 4, 0, 5], ![5, 4, 2, 3, 1, 0]] : Fin 3 → Fin 6 → Fin 6) i
  invFun := (![![0, 1, 2, 3, 4, 5], ![4, 0, 1, 2, 3, 5], ![5, 4, 2, 3, 1, 0]] : Fin 3 → Fin 6 → Fin 6) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

theorem row255_preserves : ∀ i,
    BinaryPairFrame.Preserves SixPairCyclicSymmetricSocles.pointChart (row255Generators i) (row255Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row255_matrix : ∀ i x : Fin 6,
    actualOperator representation SixPointFiveCyclePrimitive.cycle (row255Tops 2) (Pi.single i 1) x =
      operator 0 (Pi.single i 1) x := by
  decide +kernel

theorem row255AtTwo_quotientSocle (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (N : Subgroup Row255Top) [N.Normal] : SocleNormalGeneratorBound (Row255Top ⧸ N) 2 :=
  SixPairPrimitiveFinalPublishedSocles.quotientSocle_of_generators socle catalogue
    SixPairCyclicSymmetricSocles.pointChart row255Generators row255Tops 1 2 row255_preserves
    (by decide +kernel) (by decide +kernel) row255_matrix N

def row255AtTwo_family (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    row255Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row255AtTwo_quotientSocle socle catalogue N.1)

def row256Tops (i : Fin 3) : Equiv.Perm (Fin 6) where
  toFun := (![![0, 1, 2, 3, 4, 5], ![1, 2, 3, 4, 0, 5], ![5, 2, 1, 4, 3, 0]] : Fin 3 → Fin 6 → Fin 6) i
  invFun := (![![0, 1, 2, 3, 4, 5], ![4, 0, 1, 2, 3, 5], ![5, 2, 1, 4, 3, 0]] : Fin 3 → Fin 6 → Fin 6) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

theorem row256_preserves : ∀ i,
    BinaryPairFrame.Preserves SixPairCyclicSymmetricSocles.pointChart (row256Generators i) (row256Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row256_matrix : ∀ i x : Fin 6,
    actualOperator representation SixPointFiveCyclePrimitive.cycle (row256Tops 2) (Pi.single i 1) x =
      operator 0 (Pi.single i 1) x := by
  decide +kernel

theorem row256AtTwo_quotientSocle (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (N : Subgroup Row256Top) [N.Normal] : SocleNormalGeneratorBound (Row256Top ⧸ N) 2 :=
  SixPairPrimitiveFinalPublishedSocles.quotientSocle_of_generators socle catalogue
    SixPairCyclicSymmetricSocles.pointChart row256Generators row256Tops 1 2 row256_preserves
    (by decide +kernel) (by decide +kernel) row256_matrix N

def row256AtTwo_family (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    row256Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row256AtTwo_quotientSocle socle catalogue N.1)

def row257Tops (i : Fin 3) : Equiv.Perm (Fin 6) where
  toFun := (![![0, 1, 2, 3, 4, 5], ![1, 2, 3, 4, 0, 5], ![5, 2, 1, 4, 3, 0]] : Fin 3 → Fin 6 → Fin 6) i
  invFun := (![![0, 1, 2, 3, 4, 5], ![4, 0, 1, 2, 3, 5], ![5, 2, 1, 4, 3, 0]] : Fin 3 → Fin 6 → Fin 6) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

theorem row257_preserves : ∀ i,
    BinaryPairFrame.Preserves SixPairCyclicSymmetricSocles.pointChart (row257Generators i) (row257Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row257_matrix : ∀ i x : Fin 6,
    actualOperator representation SixPointFiveCyclePrimitive.cycle (row257Tops 2) (Pi.single i 1) x =
      operator 0 (Pi.single i 1) x := by
  decide +kernel

theorem row257AtTwo_quotientSocle (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (N : Subgroup Row257Top) [N.Normal] : SocleNormalGeneratorBound (Row257Top ⧸ N) 2 :=
  SixPairPrimitiveFinalPublishedSocles.quotientSocle_of_generators socle catalogue
    SixPairCyclicSymmetricSocles.pointChart row257Generators row257Tops 1 2 row257_preserves
    (by decide +kernel) (by decide +kernel) row257_matrix N

def row257AtTwo_family (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    row257Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row257AtTwo_quotientSocle socle catalogue N.1)

def row270Tops (i : Fin 3) : Equiv.Perm (Fin 6) where
  toFun := (![![0, 1, 2, 3, 4, 5], ![1, 2, 3, 4, 0, 5], ![5, 2, 1, 4, 3, 0]] : Fin 3 → Fin 6 → Fin 6) i
  invFun := (![![0, 1, 2, 3, 4, 5], ![4, 0, 1, 2, 3, 5], ![5, 2, 1, 4, 3, 0]] : Fin 3 → Fin 6 → Fin 6) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

theorem row270_preserves : ∀ i,
    BinaryPairFrame.Preserves SixPairCyclicSymmetricSocles.pointChart (row270Generators i) (row270Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row270_matrix : ∀ i x : Fin 6,
    actualOperator representation SixPointFiveCyclePrimitive.cycle (row270Tops 2) (Pi.single i 1) x =
      operator 0 (Pi.single i 1) x := by
  decide +kernel

theorem row270AtTwo_quotientSocle (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (N : Subgroup Row270Top) [N.Normal] : SocleNormalGeneratorBound (Row270Top ⧸ N) 2 :=
  SixPairPrimitiveFinalPublishedSocles.quotientSocle_of_generators socle catalogue
    SixPairCyclicSymmetricSocles.pointChart row270Generators row270Tops 1 2 row270_preserves
    (by decide +kernel) (by decide +kernel) row270_matrix N

def row270AtTwo_family (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    row270Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row270AtTwo_quotientSocle socle catalogue N.1)

def row277Tops (i : Fin 3) : Equiv.Perm (Fin 6) where
  toFun := (![![0, 1, 2, 3, 4, 5], ![1, 5, 2, 3, 4, 0], ![1, 2, 3, 4, 0, 5]] : Fin 3 → Fin 6 → Fin 6) i
  invFun := (![![0, 1, 2, 3, 4, 5], ![5, 0, 2, 3, 4, 1], ![4, 0, 1, 2, 3, 5]] : Fin 3 → Fin 6 → Fin 6) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

theorem row277_preserves : ∀ i,
    BinaryPairFrame.Preserves shiftedFrame (row277Generators i) (row277Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row277_matrix : ∀ i x : Fin 6,
    actualOperator representation SixPointFiveCyclePrimitive.cycle (row277Tops 1) (Pi.single i 1) x =
      operator 0 (Pi.single i 1) x := by
  decide +kernel

theorem row277AtTwo_quotientSocle (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (N : Subgroup Row277Top) [N.Normal] : SocleNormalGeneratorBound (Row277Top ⧸ N) 2 :=
  SixPairPrimitiveFinalPublishedSocles.quotientSocle_of_generators socle catalogue
    shiftedFrame row277Generators row277Tops 2 1 row277_preserves
    (by decide +kernel) (by decide +kernel) row277_matrix N

def row277AtTwo_family (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    row277Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row277AtTwo_quotientSocle socle catalogue N.1)

def row286Tops (i : Fin 3) : Equiv.Perm (Fin 6) where
  toFun := (![![0, 1, 2, 3, 4, 5], ![1, 5, 2, 3, 4, 0], ![1, 2, 3, 4, 0, 5]] : Fin 3 → Fin 6 → Fin 6) i
  invFun := (![![0, 1, 2, 3, 4, 5], ![5, 0, 2, 3, 4, 1], ![4, 0, 1, 2, 3, 5]] : Fin 3 → Fin 6 → Fin 6) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

theorem row286_preserves : ∀ i,
    BinaryPairFrame.Preserves shiftedFrame (row286Generators i) (row286Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row286_matrix : ∀ i x : Fin 6,
    actualOperator representation SixPointFiveCyclePrimitive.cycle (row286Tops 1) (Pi.single i 1) x =
      operator 0 (Pi.single i 1) x := by
  decide +kernel

theorem row286AtTwo_quotientSocle (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (N : Subgroup Row286Top) [N.Normal] : SocleNormalGeneratorBound (Row286Top ⧸ N) 2 :=
  SixPairPrimitiveFinalPublishedSocles.quotientSocle_of_generators socle catalogue
    shiftedFrame row286Generators row286Tops 2 1 row286_preserves
    (by decide +kernel) (by decide +kernel) row286_matrix N

def row286AtTwo_family (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    row286Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row286AtTwo_quotientSocle socle catalogue N.1)

def row287Tops (i : Fin 4) : Equiv.Perm (Fin 6) where
  toFun := (![![0, 1, 2, 3, 4, 5], ![1, 5, 2, 3, 4, 0], ![1, 2, 3, 4, 0, 5], ![5, 1, 2, 3, 4, 0]] : Fin 4 → Fin 6 → Fin 6) i
  invFun := (![![0, 1, 2, 3, 4, 5], ![5, 0, 2, 3, 4, 1], ![4, 0, 1, 2, 3, 5], ![5, 1, 2, 3, 4, 0]] : Fin 4 → Fin 6 → Fin 6) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

theorem row287_preserves : ∀ i,
    BinaryPairFrame.Preserves shiftedFrame (row287Generators i) (row287Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row287_matrix : ∀ i x : Fin 6,
    actualOperator representation SixPointFiveCyclePrimitive.cycle (row287Tops 1) (Pi.single i 1) x =
      operator 0 (Pi.single i 1) x := by
  decide +kernel

theorem row287AtTwo_quotientSocle (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (N : Subgroup Row287Top) [N.Normal] : SocleNormalGeneratorBound (Row287Top ⧸ N) 2 :=
  SixPairPrimitiveFinalPublishedSocles.quotientSocle_of_generators socle catalogue
    shiftedFrame row287Generators row287Tops 2 1 row287_preserves
    (by decide +kernel) (by decide +kernel) row287_matrix N

def row287AtTwo_family (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    row287Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row287AtTwo_quotientSocle socle catalogue N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePrimitiveFinalPublishedSocles

end
