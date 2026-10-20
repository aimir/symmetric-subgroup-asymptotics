import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopCatalogues

/-! Generated literal count-twelve pair-top catalogue from the pinned
action/module alphabet.  Completeness of each registry is semantic. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelvePairFiniteCatalogue

private def row251Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row251Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row251Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 9, 4, 11, 3, 7, 8, 6, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 6, 4, 2, 9, 7, 8, 3, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row251Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row251Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 6, 2, 7, 0, 8, 1, 3, 5, 10, 9, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 6, 2, 7, 0, 8, 1, 3, 5, 10, 9, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row251Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row251Generator0, row251Generator1, row251Generator2, row251Generator3, row251Generator4]

abbrev Row251Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row251Generators)

noncomputable def row251Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row251Top

private def row252Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row252Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row252Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 9, 4, 11, 3, 7, 8, 6, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 6, 4, 2, 9, 7, 8, 3, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row252Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row252Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row252Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row252Generator0, row252Generator1, row252Generator2, row252Generator3, row252Generator4]

abbrev Row252Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row252Generators)

noncomputable def row252Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row252Top

private def row253Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row253Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row253Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 1, 5, 3, 4, 8, 0, 7, 2, 6, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 3, 4, 2, 9, 7, 5, 0, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row253Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 10, 5, 3, 4, 2, 9, 7, 8, 6, 1, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 10, 5, 3, 4, 2, 9, 7, 8, 6, 1, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row253Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row253Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row253Generator0, row253Generator1, row253Generator2, row253Generator3, row253Generator4]

abbrev Row253Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row253Generators)

noncomputable def row253Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row253Top

private def row254Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row254Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row254Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 9, 4, 11, 3, 7, 8, 6, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 6, 4, 2, 9, 7, 8, 3, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row254Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[5, 1, 6, 11, 4, 0, 2, 10, 9, 8, 7, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[5, 1, 6, 11, 4, 0, 2, 10, 9, 8, 7, 3] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row254Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 6, 2, 7, 0, 8, 1, 3, 5, 10, 9, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 6, 2, 7, 0, 8, 1, 3, 5, 10, 9, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row254Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row254Generator0, row254Generator1, row254Generator2, row254Generator3, row254Generator4]

abbrev Row254Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row254Generators)

noncomputable def row254Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row254Top

private def row255Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row255Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 5, 6, 7, 8, 11, 0, 9, 10, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 11, 0, 1, 2, 3, 4, 5, 6, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row255Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 7, 8, 3, 4, 5, 6, 1, 2, 11, 0, 9] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 7, 8, 3, 4, 5, 6, 1, 2, 11, 0, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row255Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row255Generator0, row255Generator1, row255Generator2]

abbrev Row255Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row255Generators)

noncomputable def row255Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row255Top

private def row256Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row256Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 5, 6, 7, 8, 11, 0, 9, 10, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 11, 0, 1, 2, 3, 4, 5, 6, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row256Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 3, 4, 1, 2, 7, 8, 5, 6, 11, 0, 10] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 3, 4, 1, 2, 7, 8, 5, 6, 0, 11, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row256Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row256Generator0, row256Generator1, row256Generator2]

abbrev Row256Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row256Generators)

noncomputable def row256Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row256Top

private def row257Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row257Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 5, 6, 7, 8, 11, 0, 9, 10, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 11, 0, 1, 2, 3, 4, 5, 6, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row257Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 3, 4, 1, 2, 7, 8, 5, 6, 11, 0, 9] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 3, 4, 1, 2, 7, 8, 5, 6, 11, 0, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row257Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row257Generator0, row257Generator1, row257Generator2]

abbrev Row257Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row257Generators)

noncomputable def row257Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row257Top

private def row258Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row258Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row258Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row258Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 2, 3, 1, 8, 6, 7, 5, 0, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 2, 3, 1, 8, 6, 7, 5, 0, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row258Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row258Generator0, row258Generator1, row258Generator2, row258Generator3]

abbrev Row258Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row258Generators)

noncomputable def row258Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row258Top

private def row259Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row259Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row259Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 4, 5, 3, 10, 8, 9, 7, 2, 0, 1, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 8, 3, 1, 2, 0, 7, 5, 6, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row259Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 11, 6, 4, 9, 3, 10, 8, 5, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 6, 4, 9, 3, 10, 8, 5, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row259Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row259Generator0, row259Generator1, row259Generator2, row259Generator3]

abbrev Row259Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row259Generators)

noncomputable def row259Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row259Top

private def row260Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 3, 4, 11, 6, 7, 8, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 11, 6, 7, 8, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row260Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 2, 7, 4, 9, 6, 11, 8, 1, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 11, 4, 1, 6, 3, 8, 5, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row260Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row260Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row260Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row260Generator0, row260Generator1, row260Generator2, row260Generator3]

abbrev Row260Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row260Generators)

noncomputable def row260Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row260Top

private def row261Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row261Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 3, 8, 9, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 7, 4, 5, 6, 3, 8, 9, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row261Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row261Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row261Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row261Generator0, row261Generator1, row261Generator2, row261Generator3]

abbrev Row261Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row261Generators)

noncomputable def row261Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row261Top

private def row262Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row262Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row262Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 2, 9, 4, 11, 6, 1, 8, 3, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 7, 2, 9, 4, 11, 6, 1, 8, 3, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row262Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row262Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 0, 5, 10, 7, 8, 1, 6, 11, 4, 9, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 6, 11, 0, 9, 2, 7, 4, 5, 10, 3, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row262Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row262Generator0, row262Generator1, row262Generator2, row262Generator3, row262Generator4]

abbrev Row262Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row262Generators)

noncomputable def row262Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row262Top

private def row263Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row263Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row263Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row263Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 9, 8, 7, 10, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 9, 8, 7, 6, 5, 0, 3, 2, 1, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row263Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row263Generator0, row263Generator1, row263Generator2, row263Generator3]

abbrev Row263Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row263Generators)

noncomputable def row263Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row263Top

private def row264Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row264Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 3, 8, 9, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 7, 4, 5, 6, 3, 8, 9, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row264Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row264Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row264Generator0, row264Generator1, row264Generator2]

abbrev Row264Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row264Generators)

noncomputable def row264Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row264Top

private def row265Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 3, 4, 11, 6, 7, 8, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 2, 6, 7, 8, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row265Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 3, 4, 8, 6, 7, 2, 9, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 2, 6, 7, 5, 9, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row265Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row265Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row265Generator0, row265Generator1, row265Generator2]

abbrev Row265Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row265Generators)

noncomputable def row265Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row265Top

private def row266Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row266Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row266Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row266Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row266Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 9, 8, 7, 10, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 9, 8, 7, 6, 5, 0, 3, 2, 1, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row266Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row266Generator0, row266Generator1, row266Generator2, row266Generator3, row266Generator4]

abbrev Row266Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row266Generators)

noncomputable def row266Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row266Top

private def row267Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row267Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 10, 3, 8, 9, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 7, 4, 5, 10, 3, 8, 9, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row267Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row267Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row267Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row267Generator0, row267Generator1, row267Generator2, row267Generator3]

abbrev Row267Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row267Generators)

noncomputable def row267Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row267Top

private def row268Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row268Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row268Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 1, 5, 3, 4, 8, 0, 7, 2, 6, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 3, 4, 2, 9, 7, 5, 0, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row268Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 10, 5, 3, 4, 2, 9, 7, 8, 6, 1, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 10, 5, 3, 4, 2, 9, 7, 8, 6, 1, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row268Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row268Generator5 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row268Generators : Fin 6 → Equiv.Perm (Fin 12) :=
  ![row268Generator0, row268Generator1, row268Generator2, row268Generator3, row268Generator4, row268Generator5]

abbrev Row268Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row268Generators)

noncomputable def row268Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row268Top

private def row269Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 3, 2, 5, 4, 7, 6, 11, 8, 9, 10, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 11, 2, 1, 4, 3, 6, 5, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row269Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 2, 3, 4, 5, 6, 1, 8, 11, 10, 9] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 7, 2, 3, 4, 5, 6, 1, 8, 11, 10, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row269Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row269Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row269Generator0, row269Generator1, row269Generator2]

abbrev Row269Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row269Generators)

noncomputable def row269Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row269Top

private def row270Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row270Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 5, 6, 7, 8, 11, 0, 9, 10, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 11, 0, 1, 2, 3, 4, 5, 6, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row270Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 3, 4, 1, 2, 7, 8, 5, 6, 11, 0, 9] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 3, 4, 1, 2, 7, 8, 5, 6, 11, 0, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row270Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row270Generator0, row270Generator1, row270Generator2]

abbrev Row270Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row270Generators)

noncomputable def row270Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row270Top

private def row271Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row271Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 10, 3, 8, 9, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 7, 4, 5, 10, 3, 8, 9, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row271Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 5, 6, 4, 11, 9, 10, 8, 3, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 10, 11, 9, 4, 2, 3, 1, 8, 6, 7, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row271Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 4, 5, 3, 10, 8, 9, 7, 2, 0, 1, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 8, 3, 1, 2, 0, 7, 5, 6, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row271Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row271Generator0, row271Generator1, row271Generator2, row271Generator3]

abbrev Row271Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row271Generators)

noncomputable def row271Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row271Top

private def row272Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 10, 9, 1, 8, 11, 2, 3, 5, 4, 7, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 3, 6, 7, 9, 8, 0, 10, 4, 2, 1, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row272Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[5, 6, 8, 4, 10, 2, 11, 1, 0, 3, 7, 9] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 7, 5, 9, 3, 0, 1, 10, 2, 11, 4, 6] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row272Generators : Fin 2 → Equiv.Perm (Fin 12) :=
  ![row272Generator0, row272Generator1]

abbrev Row272Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row272Generators)

noncomputable def row272Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row272Top

private def row273Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 3, 4, 11, 6, 7, 8, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 2, 6, 7, 8, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row273Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 3, 4, 8, 6, 7, 2, 9, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 2, 6, 7, 5, 9, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row273Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 11, 6, 4, 5, 3, 10, 8, 9, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 6, 4, 5, 3, 10, 8, 9, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row273Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row273Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row273Generator0, row273Generator1, row273Generator2, row273Generator3]

abbrev Row273Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row273Generators)

noncomputable def row273Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row273Top

private def row274Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row274Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 3, 8, 9, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 7, 4, 5, 6, 3, 8, 9, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row274Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row274Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row274Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row274Generator0, row274Generator1, row274Generator2, row274Generator3]

abbrev Row274Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row274Generators)

noncomputable def row274Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row274Top

private def row275Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 3, 4, 11, 6, 7, 8, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 2, 6, 7, 8, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row275Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 3, 4, 8, 6, 7, 2, 9, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 2, 6, 7, 5, 9, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row275Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row275Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row275Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row275Generator0, row275Generator1, row275Generator2, row275Generator3]

abbrev Row275Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row275Generators)

noncomputable def row275Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row275Top

private def row276Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 3, 4, 11, 6, 7, 8, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 2, 6, 7, 8, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row276Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 3, 4, 8, 6, 7, 2, 9, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 2, 6, 7, 5, 9, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row276Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row276Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 11, 10, 0, 5, 7, 6, 8, 1, 3, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 11, 10, 0, 5, 7, 6, 8, 1, 3, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row276Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row276Generator0, row276Generator1, row276Generator2, row276Generator3]

abbrev Row276Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row276Generators)

noncomputable def row276Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row276Top

private def row277Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row277Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 11, 0, 5, 6, 7, 8, 9, 10, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 11, 0, 1, 2, 5, 6, 7, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row277Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row277Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row277Generator0, row277Generator1, row277Generator2]

abbrev Row277Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row277Generators)

noncomputable def row277Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row277Top

private def row278Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 3, 2, 5, 4, 7, 6, 11, 8, 9, 10, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 11, 2, 1, 4, 3, 6, 5, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row278Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 3, 4, 1, 2, 7, 8, 5, 6, 11, 0, 9] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 3, 4, 1, 2, 7, 8, 5, 6, 11, 0, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row278Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 4, 1, 2, 3, 8, 5, 6, 7, 0, 9, 10] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 2, 3, 4, 1, 6, 7, 8, 5, 10, 11, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row278Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row278Generator0, row278Generator1, row278Generator2]

abbrev Row278Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row278Generators)

noncomputable def row278Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row278Top

private def row279Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 3, 2, 5, 4, 7, 6, 11, 8, 9, 10, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 11, 2, 1, 4, 3, 6, 5, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row279Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 3, 4, 1, 2, 7, 8, 5, 6, 11, 0, 9] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 3, 4, 1, 2, 7, 8, 5, 6, 11, 0, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row279Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row279Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row279Generator0, row279Generator1, row279Generator2]

abbrev Row279Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row279Generators)

noncomputable def row279Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row279Top

private def row280Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row280Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 3, 8, 9, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 7, 4, 5, 6, 3, 8, 9, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row280Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 5, 6, 4, 11, 9, 10, 8, 3, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 10, 11, 9, 4, 2, 3, 1, 8, 6, 7, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row280Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 4, 5, 3, 10, 8, 9, 7, 2, 0, 1, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 8, 3, 1, 2, 0, 7, 5, 6, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row280Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row280Generator0, row280Generator1, row280Generator2, row280Generator3]

abbrev Row280Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row280Generators)

noncomputable def row280Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row280Top

private def row281Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row281Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 10, 3, 8, 9, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 7, 4, 5, 10, 3, 8, 9, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row281Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row281Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 10, 5, 3, 4, 2, 9, 7, 8, 6, 1, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 10, 5, 3, 4, 2, 9, 7, 8, 6, 1, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row281Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row281Generator0, row281Generator1, row281Generator2, row281Generator3]

abbrev Row281Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row281Generators)

noncomputable def row281Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row281Top

private def row282Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row282Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row282Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 5, 6, 4, 11, 9, 10, 8, 3, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 10, 11, 9, 4, 2, 3, 1, 8, 6, 7, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row282Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 4, 5, 3, 10, 8, 9, 7, 2, 0, 1, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 8, 3, 1, 2, 0, 7, 5, 6, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row282Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 9, 8, 7, 10, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 9, 8, 7, 6, 5, 0, 3, 2, 1, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row282Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row282Generator0, row282Generator1, row282Generator2, row282Generator3, row282Generator4]

abbrev Row282Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row282Generators)

noncomputable def row282Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row282Top

private def row283Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 3, 4, 11, 6, 7, 8, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 2, 6, 7, 8, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row283Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 3, 4, 8, 6, 7, 2, 9, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 2, 6, 7, 5, 9, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row283Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 11, 6, 4, 5, 3, 10, 8, 9, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 6, 4, 5, 3, 10, 8, 9, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row283Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row283Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row283Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row283Generator0, row283Generator1, row283Generator2, row283Generator3, row283Generator4]

abbrev Row283Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row283Generators)

noncomputable def row283Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row283Top

private def row284Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 3, 4, 11, 6, 7, 8, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 2, 6, 7, 8, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row284Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 3, 4, 8, 6, 7, 2, 9, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 2, 6, 7, 5, 9, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row284Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 11, 6, 4, 5, 3, 7, 8, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 6, 4, 5, 3, 7, 8, 9, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row284Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row284Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row284Generator0, row284Generator1, row284Generator2, row284Generator3]

abbrev Row284Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row284Generators)

noncomputable def row284Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row284Top

private def row285Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row285Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 11, 0, 3, 4, 5, 6, 7, 8, 9, 10, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[2, 11, 0, 3, 4, 5, 6, 7, 8, 9, 10, 1] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row285Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row285Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row285Generator0, row285Generator1, row285Generator2]

abbrev Row285Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row285Generators)

noncomputable def row285Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row285Top

private def row286Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row286Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 11, 0, 5, 6, 7, 8, 9, 10, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 11, 0, 1, 2, 5, 6, 7, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row286Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row286Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row286Generator0, row286Generator1, row286Generator2]

abbrev Row286Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row286Generators)

noncomputable def row286Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row286Top

private def row287Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row287Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 11, 0, 5, 6, 7, 8, 9, 10, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 11, 0, 1, 2, 5, 6, 7, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row287Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row287Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 11, 0, 3, 4, 5, 6, 7, 8, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[2, 0, 11, 3, 4, 5, 6, 7, 8, 9, 10, 1] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row287Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row287Generator0, row287Generator1, row287Generator2, row287Generator3]

abbrev Row287Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row287Generators)

noncomputable def row287Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row287Top

private def row288Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 3, 2, 5, 4, 7, 6, 11, 8, 9, 10, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 11, 2, 1, 4, 3, 6, 5, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row288Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 3, 2, 1, 4, 7, 6, 5, 8, 11, 10, 9] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 3, 2, 1, 4, 7, 6, 5, 8, 11, 10, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row288Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row288Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row288Generator0, row288Generator1, row288Generator2]

abbrev Row288Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row288Generators)

noncomputable def row288Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row288Top

private def row289Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row289Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 3, 8, 9, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 7, 4, 5, 6, 3, 8, 9, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row289Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row289Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 2, 3, 1, 8, 6, 7, 5, 0, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 2, 3, 1, 8, 6, 7, 5, 0, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row289Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row289Generator0, row289Generator1, row289Generator2, row289Generator3]

abbrev Row289Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row289Generators)

noncomputable def row289Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row289Top

private def row290Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 3, 4, 11, 6, 7, 8, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 2, 6, 7, 8, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row290Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 3, 4, 8, 6, 7, 2, 9, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 2, 6, 7, 5, 9, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row290Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 11, 6, 4, 5, 3, 7, 8, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 6, 4, 5, 3, 7, 8, 9, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row290Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row290Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row290Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row290Generator0, row290Generator1, row290Generator2, row290Generator3, row290Generator4]

abbrev Row290Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row290Generators)

noncomputable def row290Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row290Top

private def row291Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 3, 4, 11, 6, 7, 8, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 2, 6, 7, 8, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row291Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 3, 4, 8, 6, 7, 2, 9, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 2, 6, 7, 5, 9, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row291Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 1, 2, 3, 4, 8, 6, 7, 5, 0, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 1, 2, 3, 4, 8, 6, 7, 5, 0, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row291Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row291Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 0, 2, 7, 9, 8, 10, 3, 5, 4, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 0, 2, 7, 9, 8, 10, 3, 5, 4, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row291Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row291Generator0, row291Generator1, row291Generator2, row291Generator3, row291Generator4]

abbrev Row291Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row291Generators)

noncomputable def row291Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row291Top

private def row292Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 3, 4, 8, 6, 7, 11, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 2, 6, 7, 5, 9, 10, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row292Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 3, 4, 8, 6, 7, 5, 9, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 8, 6, 7, 5, 9, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row292Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row292Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row292Generator0, row292Generator1, row292Generator2]

abbrev Row292Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row292Generators)

noncomputable def row292Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row292Top

private def row293Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row293Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 11, 0, 3, 4, 5, 6, 7, 8, 9, 10, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[2, 11, 0, 3, 4, 5, 6, 7, 8, 9, 10, 1] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row293Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row293Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row293Generator0, row293Generator1, row293Generator2]

abbrev Row293Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row293Generators)

noncomputable def row293Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row293Top

private def row294Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 3, 4, 8, 6, 7, 11, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 2, 6, 7, 5, 9, 10, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row294Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 3, 4, 8, 6, 7, 5, 9, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 8, 6, 7, 5, 9, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row294Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row294Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row294Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row294Generator0, row294Generator1, row294Generator2, row294Generator3]

abbrev Row294Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row294Generators)

noncomputable def row294Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row294Top

private def row295Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 2, 3, 0, 7, 6, 4, 11, 8, 9, 1, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[3, 10, 1, 2, 6, 11, 5, 4, 8, 9, 0, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row295Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[8, 3, 2, 0, 11, 9, 6, 1, 4, 5, 7, 10] : Array (Fin 12))[x.val]!
  invFun x := (#[3, 7, 2, 1, 8, 9, 6, 10, 0, 5, 11, 4] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row295Generators : Fin 2 → Equiv.Perm (Fin 12) :=
  ![row295Generator0, row295Generator1]

abbrev Row295Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row295Generators)

noncomputable def row295Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row295Top

private def row296Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 3, 2, 11, 4, 5, 6, 7, 8, 9, 10, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 11, 2, 1, 4, 5, 6, 7, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row296Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 3, 2, 5, 4, 7, 6, 9, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 1, 4, 3, 6, 5, 8, 7, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row296Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row296Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row296Generator0, row296Generator1, row296Generator2]

abbrev Row296Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row296Generators)

noncomputable def row296Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row296Top

private def row297Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 3, 2, 5, 4, 7, 6, 9, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 1, 4, 3, 6, 5, 8, 7, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row297Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 3, 2, 11, 4, 5, 6, 7, 8, 9, 10, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 11, 2, 1, 4, 5, 6, 7, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row297Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 11, 0, 3, 4, 5, 6, 7, 8, 9, 10, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[2, 11, 0, 3, 4, 5, 6, 7, 8, 9, 10, 1] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row297Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row297Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row297Generator0, row297Generator1, row297Generator2, row297Generator3]

abbrev Row297Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row297Generators)

noncomputable def row297Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row297Top

private def row298Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 3, 2, 11, 4, 5, 6, 7, 8, 9, 10, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 11, 2, 1, 4, 5, 6, 7, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row298Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 3, 2, 5, 4, 7, 6, 9, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 1, 4, 3, 6, 5, 8, 7, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row298Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 11, 0, 3, 4, 5, 6, 7, 8, 9, 10, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[2, 11, 0, 3, 4, 5, 6, 7, 8, 9, 10, 1] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row298Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 0, 1, 4, 3, 6, 5, 8, 7, 10, 9, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 2, 11, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row298Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row298Generator0, row298Generator1, row298Generator2, row298Generator3]

abbrev Row298Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row298Generators)

noncomputable def row298Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row298Top

private def row299Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 11, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 11, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row299Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row299Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row299Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row299Generator0, row299Generator1, row299Generator2]

abbrev Row299Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row299Generators)

noncomputable def row299Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row299Top

private def row300Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row300Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 9] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 9, 10] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row300Generators : Fin 2 → Equiv.Perm (Fin 12) :=
  ![row300Generator0, row300Generator1]

abbrev Row300Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row300Generators)

noncomputable def row300Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row300Top

private def row301Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row301Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row301Generators : Fin 2 → Equiv.Perm (Fin 12) :=
  ![row301Generator0, row301Generator1]

abbrev Row301Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row301Generators)

noncomputable def row301Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row301Top

end DegreeTwoTwelvePairFiniteCatalogue
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
