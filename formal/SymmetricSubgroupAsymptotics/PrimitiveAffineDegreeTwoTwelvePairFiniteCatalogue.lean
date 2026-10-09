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

private def row1Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row1Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row1Generators : Fin 2 → Equiv.Perm (Fin 12) :=
  ![row1Generator0, row1Generator1]

abbrev Row1Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row1Generators)

noncomputable def row1Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row1Top

private def row2Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row2Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row2Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row2Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row2Generator0, row2Generator1, row2Generator2]

abbrev Row2Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row2Generators)

noncomputable def row2Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row2Top

private def row3Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row3Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 7, 8, 5, 6, 3, 4, 1, 2, 11, 0, 9] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 7, 8, 5, 6, 3, 4, 1, 2, 11, 0, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row3Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row3Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row3Generator0, row3Generator1, row3Generator2]

abbrev Row3Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row3Generators)

noncomputable def row3Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row3Top

private def row4Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[8, 3, 1, 2, 0, 7, 5, 6, 4, 11, 9, 10] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 2, 3, 1, 8, 6, 7, 5, 0, 10, 11, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row4Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 8, 9, 7, 2, 0, 1, 11, 6, 4, 5, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[5, 6, 4, 11, 9, 10, 8, 3, 1, 2, 0, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row4Generators : Fin 2 → Equiv.Perm (Fin 12) :=
  ![row4Generator0, row4Generator1]

abbrev Row4Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row4Generators)

noncomputable def row4Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row4Top

private def row5Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row5Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row5Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[7, 0, 5, 10, 3, 8, 1, 6, 11, 4, 9, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 6, 11, 4, 9, 2, 7, 0, 5, 10, 3, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row5Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row5Generator0, row5Generator1, row5Generator2]

abbrev Row5Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row5Generators)

noncomputable def row5Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row5Top

private def row6Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[8, 3, 1, 2, 0, 7, 5, 6, 4, 11, 9, 10] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 2, 3, 1, 8, 6, 7, 5, 0, 10, 11, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row6Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 8, 9, 7, 2, 0, 1, 11, 6, 4, 5, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[5, 6, 4, 11, 9, 10, 8, 3, 1, 2, 0, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row6Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 10, 11, 9, 7, 8, 0, 4, 5, 3, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 10, 11, 9, 7, 8, 0, 4, 5, 3, 1, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row6Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row6Generator0, row6Generator1, row6Generator2]

abbrev Row6Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row6Generators)

noncomputable def row6Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row6Top

private def row7Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row7Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row7Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row7Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row7Generator0, row7Generator1, row7Generator2]

abbrev Row7Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row7Generators)

noncomputable def row7Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row7Top

private def row8Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 0, 4, 5, 2, 3, 8, 9, 6, 7, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 0, 4, 5, 2, 3, 8, 9, 6, 7, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row8Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 5, 6, 7, 11, 9, 10, 4, 1, 8, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 9, 0, 1, 8, 2, 3, 4, 10, 6, 7, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row8Generators : Fin 2 → Equiv.Perm (Fin 12) :=
  ![row8Generator0, row8Generator1]

abbrev Row8Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row8Generators)

noncomputable def row8Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row8Top

private def row9Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 9, 4, 11, 0, 7, 2, 3, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 9, 4, 11, 0, 7, 2, 3, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row9Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row9Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 0, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 0, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row9Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row9Generator0, row9Generator1, row9Generator2]

abbrev Row9Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row9Generators)

noncomputable def row9Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row9Top

private def row10Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row10Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row10Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row10Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row10Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row10Generator0, row10Generator1, row10Generator2, row10Generator3]

abbrev Row10Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row10Generators)

noncomputable def row10Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row10Top

private def row11Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row11Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row11Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row11Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row11Generator0, row11Generator1, row11Generator2]

abbrev Row11Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row11Generators)

noncomputable def row11Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row11Top

private def row12Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row12Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row12Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row12Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row12Generator0, row12Generator1, row12Generator2]

abbrev Row12Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row12Generators)

noncomputable def row12Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row12Top

private def row13Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row13Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row13Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row13Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row13Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row13Generator0, row13Generator1, row13Generator2, row13Generator3]

abbrev Row13Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row13Generators)

noncomputable def row13Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row13Top

private def row14Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row14Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row14Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row14Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row14Generator0, row14Generator1, row14Generator2]

abbrev Row14Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row14Generators)

noncomputable def row14Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row14Top

private def row15Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row15Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 2, 9, 4, 11, 6, 1, 8, 3, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 7, 2, 9, 4, 11, 6, 1, 8, 3, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row15Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row15Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 0, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 0, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row15Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row15Generator0, row15Generator1, row15Generator2, row15Generator3]

abbrev Row15Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row15Generators)

noncomputable def row15Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row15Top

private def row16Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 2, 7, 4, 1, 6, 11, 8, 5, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 5, 2, 11, 4, 9, 6, 3, 8, 1, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row16Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row16Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row16Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row16Generator0, row16Generator1, row16Generator2]

abbrev Row16Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row16Generators)

noncomputable def row16Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row16Top

private def row17Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 2, 7, 4, 1, 6, 11, 8, 5, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 5, 2, 11, 4, 9, 6, 3, 8, 1, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row17Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row17Generators : Fin 2 → Equiv.Perm (Fin 12) :=
  ![row17Generator0, row17Generator1]

abbrev Row17Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row17Generators)

noncomputable def row17Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row17Top

private def row18Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 2, 7, 4, 9, 6, 11, 8, 1, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 11, 4, 1, 6, 3, 8, 5, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row18Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row18Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row18Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row18Generator0, row18Generator1, row18Generator2]

abbrev Row18Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row18Generators)

noncomputable def row18Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row18Top

private def row19Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 2, 7, 4, 9, 6, 11, 8, 1, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 11, 4, 1, 6, 3, 8, 5, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row19Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row19Generators : Fin 2 → Equiv.Perm (Fin 12) :=
  ![row19Generator0, row19Generator1]

abbrev Row19Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row19Generators)

noncomputable def row19Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row19Top

private def row20Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 5, 6, 4, 11, 9, 10, 8, 3, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 10, 11, 9, 4, 2, 3, 1, 8, 6, 7, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row20Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 4, 5, 3, 10, 8, 9, 7, 2, 0, 1, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 8, 3, 1, 2, 0, 7, 5, 6, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row20Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row20Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row20Generator0, row20Generator1, row20Generator2]

abbrev Row20Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row20Generators)

noncomputable def row20Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row20Top

private def row21Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row21Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row21Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 0, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 0, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row21Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row21Generator0, row21Generator1, row21Generator2]

abbrev Row21Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row21Generators)

noncomputable def row21Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row21Top

private def row22Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 0, 4, 5, 2, 3, 8, 9, 6, 7, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 0, 4, 5, 2, 3, 8, 9, 6, 7, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row22Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 5, 6, 7, 11, 9, 10, 4, 1, 8, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 9, 0, 1, 8, 2, 3, 4, 10, 6, 7, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row22Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[8, 6, 4, 9, 2, 7, 1, 5, 0, 3, 11, 10] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 6, 4, 9, 2, 7, 1, 5, 0, 3, 11, 10] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row22Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row22Generator0, row22Generator1, row22Generator2]

abbrev Row22Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row22Generators)

noncomputable def row22Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row22Top

private def row23Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row23Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row23Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row23Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row23Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row23Generator0, row23Generator1, row23Generator2, row23Generator3]

abbrev Row23Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row23Generators)

noncomputable def row23Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row23Top

private def row24Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row24Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row24Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 9, 10, 7, 8, 11, 0, 3, 4, 1, 2, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 9, 10, 7, 8, 11, 0, 3, 4, 1, 2, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row24Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row24Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row24Generator0, row24Generator1, row24Generator2, row24Generator3]

abbrev Row24Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row24Generators)

noncomputable def row24Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row24Top

private def row25Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 2, 3, 4, 11, 0, 7, 8, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 2, 3, 4, 11, 0, 7, 8, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row25Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row25Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row25Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row25Generator0, row25Generator1, row25Generator2]

abbrev Row25Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row25Generators)

noncomputable def row25Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row25Top

private def row26Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[8, 3, 1, 2, 0, 7, 5, 6, 4, 11, 9, 10] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 2, 3, 1, 8, 6, 7, 5, 0, 10, 11, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row26Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 8, 9, 7, 2, 0, 1, 11, 6, 4, 5, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[5, 6, 4, 11, 9, 10, 8, 3, 1, 2, 0, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row26Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 10, 11, 9, 7, 8, 0, 4, 5, 3, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 10, 11, 9, 7, 8, 0, 4, 5, 3, 1, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row26Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 8, 0, 1, 11, 9, 10, 2, 6, 7, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[3, 4, 8, 0, 1, 11, 9, 10, 2, 6, 7, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row26Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row26Generator0, row26Generator1, row26Generator2, row26Generator3]

abbrev Row26Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row26Generators)

noncomputable def row26Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row26Top

private def row27Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 10, 11, 9, 7, 8, 0, 4, 5, 3, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 10, 11, 9, 7, 8, 0, 4, 5, 3, 1, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row27Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[8, 3, 1, 2, 0, 7, 5, 6, 4, 11, 9, 10] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 2, 3, 1, 8, 6, 7, 5, 0, 10, 11, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row27Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 8, 9, 7, 2, 0, 1, 11, 6, 4, 5, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[5, 6, 4, 11, 9, 10, 8, 3, 1, 2, 0, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row27Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 2, 10, 6, 5, 7, 9, 8, 4, 0, 11, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 11, 1, 0, 8, 4, 3, 5, 7, 6, 2, 10] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row27Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row27Generator0, row27Generator1, row27Generator2, row27Generator3]

abbrev Row27Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row27Generators)

noncomputable def row27Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row27Top

private def row28Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row28Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row28Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row28Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row28Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row28Generator0, row28Generator1, row28Generator2, row28Generator3]

abbrev Row28Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row28Generators)

noncomputable def row28Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row28Top

private def row29Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 9, 4, 11, 0, 7, 2, 3, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 9, 4, 11, 0, 7, 2, 3, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row29Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row29Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row29Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row29Generator0, row29Generator1, row29Generator2]

abbrev Row29Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row29Generators)

noncomputable def row29Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row29Top

private def row30Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row30Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row30Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[7, 0, 5, 10, 3, 8, 1, 6, 11, 4, 9, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 6, 11, 4, 9, 2, 7, 0, 5, 10, 3, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row30Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row30Generator0, row30Generator1, row30Generator2]

abbrev Row30Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row30Generators)

noncomputable def row30Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row30Top

private def row31Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 1, 5, 0, 4, 8, 3, 7, 11, 6, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[3, 1, 11, 6, 4, 2, 9, 7, 5, 0, 10, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row31Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row31Generators : Fin 2 → Equiv.Perm (Fin 12) :=
  ![row31Generator0, row31Generator1]

abbrev Row31Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row31Generators)

noncomputable def row31Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row31Top

private def row32Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 1, 11, 6, 4, 8, 3, 7, 5, 0, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 1, 11, 6, 4, 8, 3, 7, 5, 0, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row32Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 9, 4, 11, 0, 7, 2, 3, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 9, 4, 11, 0, 7, 2, 3, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row32Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row32Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row32Generator0, row32Generator1, row32Generator2]

abbrev Row32Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row32Generators)

noncomputable def row32Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row32Top

private def row33Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 5, 6, 7, 8, 11, 0, 9, 10, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 11, 0, 1, 2, 3, 4, 5, 6, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row33Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 6, 5, 11, 0, 7, 8, 2, 1, 3, 4, 9] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 8, 7, 9, 10, 2, 1, 5, 6, 11, 0, 3] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row33Generators : Fin 2 → Equiv.Perm (Fin 12) :=
  ![row33Generator0, row33Generator1]

abbrev Row33Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row33Generators)

noncomputable def row33Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row33Top

private def row34Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row34Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[7, 2, 1, 4, 3, 6, 5, 0, 11, 10, 9, 8] : Array (Fin 12))[x.val]!
  invFun x := (#[7, 2, 1, 4, 3, 6, 5, 0, 11, 10, 9, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row34Generators : Fin 2 → Equiv.Perm (Fin 12) :=
  ![row34Generator0, row34Generator1]

abbrev Row34Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row34Generators)

noncomputable def row34Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row34Top

private def row35Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 2, 7, 4, 9, 6, 11, 8, 1, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 11, 4, 1, 6, 3, 8, 5, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row35Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 2, 5, 4, 3, 6, 1, 8, 11, 10, 9] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 7, 2, 5, 4, 3, 6, 1, 8, 11, 10, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row35Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row35Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row35Generator0, row35Generator1, row35Generator2]

abbrev Row35Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row35Generators)

noncomputable def row35Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row35Top

private def row36Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row36Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[8, 2, 1, 3, 4, 6, 5, 11, 0, 10, 9, 7] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 2, 1, 3, 4, 6, 5, 11, 0, 10, 9, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row36Generators : Fin 2 → Equiv.Perm (Fin 12) :=
  ![row36Generator0, row36Generator1]

abbrev Row36Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row36Generators)

noncomputable def row36Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row36Top

private def row37Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 2, 7, 4, 9, 6, 11, 8, 1, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 11, 4, 1, 6, 3, 8, 5, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row37Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row37Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row37Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row37Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row37Generator0, row37Generator1, row37Generator2, row37Generator3]

abbrev Row37Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row37Generators)

noncomputable def row37Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row37Top

private def row38Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 2, 7, 4, 9, 6, 11, 8, 1, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 11, 4, 1, 6, 3, 8, 5, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row38Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row38Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row38Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row38Generator0, row38Generator1, row38Generator2]

abbrev Row38Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row38Generators)

noncomputable def row38Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row38Top

private def row39Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 2, 7, 4, 9, 6, 11, 8, 1, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 11, 4, 1, 6, 3, 8, 5, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row39Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row39Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row39Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row39Generator0, row39Generator1, row39Generator2]

abbrev Row39Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row39Generators)

noncomputable def row39Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row39Top

private def row40Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 1, 2, 7, 8, 5, 6, 11, 0, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 1, 2, 11, 0, 5, 6, 3, 4, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row40Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row40Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 1, 2, 11, 0, 9, 10, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 3, 4, 9, 10, 11, 0, 1, 2, 7, 8, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row40Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row40Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row40Generator0, row40Generator1, row40Generator2, row40Generator3]

abbrev Row40Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row40Generators)

noncomputable def row40Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row40Top

private def row41Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row41Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 1, 2, 7, 8, 5, 6, 11, 0, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 1, 2, 11, 0, 5, 6, 3, 4, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row41Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row41Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[5, 7, 8, 2, 1, 11, 0, 10, 9, 3, 4, 6] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 4, 3, 9, 10, 0, 11, 1, 2, 8, 7, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row41Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row41Generator0, row41Generator1, row41Generator2, row41Generator3]

abbrev Row41Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row41Generators)

noncomputable def row41Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row41Top

private def row42Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 2, 7, 4, 9, 6, 11, 8, 1, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 11, 4, 1, 6, 3, 8, 5, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row42Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row42Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row42Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row42Generator0, row42Generator1, row42Generator2]

abbrev Row42Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row42Generators)

noncomputable def row42Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row42Top

private def row43Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 5, 6, 4, 11, 9, 10, 8, 3, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 10, 11, 9, 4, 2, 3, 1, 8, 6, 7, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row43Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 4, 5, 3, 10, 8, 9, 7, 2, 0, 1, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 8, 3, 1, 2, 0, 7, 5, 6, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row43Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row43Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row43Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row43Generator0, row43Generator1, row43Generator2, row43Generator3]

abbrev Row43Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row43Generators)

noncomputable def row43Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row43Top

private def row44Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row44Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 5, 6, 4, 11, 9, 10, 8, 3, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 10, 11, 9, 4, 2, 3, 1, 8, 6, 7, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row44Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 4, 5, 3, 10, 8, 9, 7, 2, 0, 1, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 8, 3, 1, 2, 0, 7, 5, 6, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row44Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row44Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row44Generator0, row44Generator1, row44Generator2, row44Generator3]

abbrev Row44Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row44Generators)

noncomputable def row44Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row44Top

private def row45Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row45Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 2, 3, 1, 8, 6, 7, 5, 0, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 2, 3, 1, 8, 6, 7, 5, 0, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row45Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row45Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row45Generator0, row45Generator1, row45Generator2]

abbrev Row45Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row45Generators)

noncomputable def row45Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row45Top

private def row46Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 7, 4, 9, 10, 11, 8, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 11, 4, 1, 2, 3, 8, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row46Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row46Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 10, 8, 1, 7, 2, 0, 9, 11, 6, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 3, 5, 0, 10, 11, 9, 4, 2, 7, 1, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row46Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row46Generator0, row46Generator1, row46Generator2]

abbrev Row46Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row46Generators)

noncomputable def row46Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row46Top

private def row47Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 7, 4, 9, 10, 11, 8, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 11, 4, 1, 2, 3, 8, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row47Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row47Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 4, 11, 10, 9, 8, 3, 6, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 0, 11, 6, 1, 8, 7, 10, 5, 4, 3, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row47Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 6, 5, 4, 7, 2, 9, 0, 11, 10, 1, 8] : Array (Fin 12))[x.val]!
  invFun x := (#[7, 10, 5, 0, 3, 2, 1, 4, 11, 6, 9, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row47Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row47Generator0, row47Generator1, row47Generator2, row47Generator3]

abbrev Row47Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row47Generators)

noncomputable def row47Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row47Top

private def row48Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 2, 3, 4, 11, 0, 7, 8, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 2, 3, 4, 11, 0, 7, 8, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row48Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row48Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row48Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row48Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row48Generator0, row48Generator1, row48Generator2, row48Generator3]

abbrev Row48Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row48Generators)

noncomputable def row48Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row48Top

private def row49Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[8, 6, 4, 9, 2, 7, 1, 5, 0, 3, 11, 10] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 6, 4, 9, 2, 7, 1, 5, 0, 3, 11, 10] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row49Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 0, 4, 5, 2, 3, 8, 9, 6, 7, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 0, 4, 5, 2, 3, 8, 9, 6, 7, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row49Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 5, 6, 7, 11, 9, 10, 4, 1, 8, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 9, 0, 1, 8, 2, 3, 4, 10, 6, 7, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row49Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 8, 10, 7, 11, 3, 0, 9, 6, 5, 4, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 0, 11, 5, 10, 9, 8, 3, 1, 7, 2, 4] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row49Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row49Generator0, row49Generator1, row49Generator2, row49Generator3]

abbrev Row49Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row49Generators)

noncomputable def row49Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row49Top

private def row50Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row50Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row50Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row50Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 0, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 0, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row50Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row50Generator0, row50Generator1, row50Generator2, row50Generator3]

abbrev Row50Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row50Generators)

noncomputable def row50Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row50Top

private def row51Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row51Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row51Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row51Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row51Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row51Generator0, row51Generator1, row51Generator2, row51Generator3]

abbrev Row51Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row51Generators)

noncomputable def row51Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row51Top

private def row52Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row52Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row52Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row52Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row52Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row52Generator0, row52Generator1, row52Generator2, row52Generator3]

abbrev Row52Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row52Generators)

noncomputable def row52Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row52Top

private def row53Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 9, 4, 11, 0, 7, 2, 3, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 9, 4, 11, 0, 7, 2, 3, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row53Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row53Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row53Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row53Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row53Generator0, row53Generator1, row53Generator2, row53Generator3]

abbrev Row53Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row53Generators)

noncomputable def row53Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row53Top

private def row54Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row54Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row54Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 2, 1, 8, 7, 9, 10, 4, 3, 5, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 2, 1, 8, 7, 9, 10, 4, 3, 5, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row54Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 0, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 0, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row54Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row54Generator0, row54Generator1, row54Generator2, row54Generator3]

abbrev Row54Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row54Generators)

noncomputable def row54Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row54Top

private def row55Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row55Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 1, 5, 0, 4, 8, 3, 7, 11, 6, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[3, 1, 11, 6, 4, 2, 9, 7, 5, 0, 10, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row55Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row55Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row55Generator0, row55Generator1, row55Generator2]

abbrev Row55Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row55Generators)

noncomputable def row55Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row55Top

private def row56Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row56Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 1, 11, 6, 4, 8, 3, 7, 5, 0, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 1, 11, 6, 4, 8, 3, 7, 5, 0, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row56Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row56Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row56Generator0, row56Generator1, row56Generator2]

abbrev Row56Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row56Generators)

noncomputable def row56Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row56Top

private def row57Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row57Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row57Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 11, 0, 6, 5, 4, 3, 8, 7, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[2, 0, 11, 6, 5, 4, 3, 8, 7, 9, 10, 1] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row57Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row57Generator0, row57Generator1, row57Generator2]

abbrev Row57Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row57Generators)

noncomputable def row57Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row57Top

private def row58Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row58Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 3, 4, 5, 6, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 3, 4, 5, 6, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row58Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row58Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row58Generator0, row58Generator1, row58Generator2]

abbrev Row58Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row58Generators)

noncomputable def row58Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row58Top

private def row59Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 6, 5, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 6, 5, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row59Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row59Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row59Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row59Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row59Generator0, row59Generator1, row59Generator2, row59Generator3]

abbrev Row59Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row59Generators)

noncomputable def row59Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row59Top

private def row60Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 6, 5, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 6, 5, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row60Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row60Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 9, 10, 6, 5, 8, 7, 3, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 9, 10, 6, 5, 8, 7, 3, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row60Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row60Generator0, row60Generator1, row60Generator2]

abbrev Row60Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row60Generators)

noncomputable def row60Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row60Top

private def row61Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 6, 5, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 6, 5, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row61Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row61Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row61Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 8, 10, 9, 6, 5, 1, 2, 4, 3, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 7, 8, 10, 9, 6, 5, 1, 2, 4, 3, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row61Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row61Generator0, row61Generator1, row61Generator2, row61Generator3]

abbrev Row61Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row61Generators)

noncomputable def row61Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row61Top

private def row62Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 1, 5, 0, 4, 8, 3, 7, 11, 6, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[3, 1, 11, 6, 4, 2, 9, 7, 5, 0, 10, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row62Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row62Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row62Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row62Generator0, row62Generator1, row62Generator2]

abbrev Row62Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row62Generators)

noncomputable def row62Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row62Top

private def row63Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 6, 5, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 6, 5, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row63Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row63Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 0, 11, 4, 3, 7, 8, 5, 6, 10, 9, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 0, 11, 4, 3, 7, 8, 5, 6, 10, 9, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row63Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row63Generator0, row63Generator1, row63Generator2]

abbrev Row63Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row63Generators)

noncomputable def row63Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row63Top

private def row64Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 6, 5, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 6, 5, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row64Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row64Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 0, 11, 4, 3, 8, 7, 6, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 0, 11, 4, 3, 8, 7, 6, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row64Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row64Generator0, row64Generator1, row64Generator2]

abbrev Row64Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row64Generators)

noncomputable def row64Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row64Top

private def row65Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 6, 5, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 6, 5, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row65Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row65Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 11, 0, 9, 10, 7, 8, 5, 6, 3, 4, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[2, 11, 0, 9, 10, 7, 8, 5, 6, 3, 4, 1] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row65Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 8, 7, 11, 0, 10, 9, 2, 1, 6, 5, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 8, 7, 11, 0, 10, 9, 2, 1, 6, 5, 3] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row65Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row65Generator0, row65Generator1, row65Generator2, row65Generator3]

abbrev Row65Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row65Generators)

noncomputable def row65Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row65Top

private def row66Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 6, 5, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 6, 5, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row66Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row66Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 11, 0, 7, 8, 9, 10, 5, 6, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 11, 0, 1, 2, 9, 10, 5, 6, 7, 8, 3] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row66Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 3, 4, 1, 2, 6, 5, 10, 9, 8, 7, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 3, 4, 1, 2, 6, 5, 10, 9, 8, 7, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row66Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row66Generator0, row66Generator1, row66Generator2, row66Generator3]

abbrev Row66Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row66Generators)

noncomputable def row66Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row66Top

private def row67Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 1, 11, 6, 4, 8, 3, 7, 5, 0, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 1, 11, 6, 4, 8, 3, 7, 5, 0, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row67Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 9, 4, 11, 0, 7, 2, 3, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 9, 4, 11, 0, 7, 2, 3, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row67Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row67Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row67Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row67Generator0, row67Generator1, row67Generator2, row67Generator3]

abbrev Row67Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row67Generators)

noncomputable def row67Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row67Top

private def row68Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 6, 5, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 6, 5, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row68Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row68Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row68Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 9, 10, 7, 8, 11, 0, 3, 4, 1, 2, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 9, 10, 7, 8, 11, 0, 3, 4, 1, 2, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row68Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row68Generator0, row68Generator1, row68Generator2, row68Generator3]

abbrev Row68Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row68Generators)

noncomputable def row68Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row68Top

private def row69Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row69Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 3, 4, 5, 6, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 3, 4, 5, 6, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row69Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row69Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 7, 8, 5, 6, 3, 4, 1, 2, 11, 0, 9] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 7, 8, 5, 6, 3, 4, 1, 2, 11, 0, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row69Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row69Generator0, row69Generator1, row69Generator2, row69Generator3]

abbrev Row69Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row69Generators)

noncomputable def row69Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row69Top

private def row70Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 7, 4, 9, 10, 11, 8, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 11, 4, 1, 2, 3, 8, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row70Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 0, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 0, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row70Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row70Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row70Generator0, row70Generator1, row70Generator2]

abbrev Row70Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row70Generators)

noncomputable def row70Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row70Top

private def row71Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 7, 4, 9, 10, 11, 8, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 11, 4, 1, 2, 3, 8, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row71Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row71Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row71Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row71Generator0, row71Generator1, row71Generator2]

abbrev Row71Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row71Generators)

noncomputable def row71Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row71Top

private def row72Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 7, 4, 9, 10, 11, 8, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 11, 4, 1, 2, 3, 8, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row72Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row72Generators : Fin 2 → Equiv.Perm (Fin 12) :=
  ![row72Generator0, row72Generator1]

abbrev Row72Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row72Generators)

noncomputable def row72Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row72Top

private def row73Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 7, 4, 9, 10, 11, 8, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 11, 4, 1, 2, 3, 8, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row73Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row73Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[7, 0, 5, 10, 3, 8, 1, 6, 11, 4, 9, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 6, 11, 4, 9, 2, 7, 0, 5, 10, 3, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row73Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row73Generator0, row73Generator1, row73Generator2]

abbrev Row73Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row73Generators)

noncomputable def row73Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row73Top

private def row74Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row74Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 6, 11, 4, 3, 10, 1, 8, 7, 0, 5, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 6, 11, 4, 3, 10, 1, 8, 7, 0, 5, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row74Generators : Fin 2 → Equiv.Perm (Fin 12) :=
  ![row74Generator0, row74Generator1]

abbrev Row74Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row74Generators)

noncomputable def row74Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row74Top

private def row75Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 5, 6, 7, 8, 11, 0, 9, 10, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 11, 0, 1, 2, 3, 4, 5, 6, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row75Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 7, 8, 3, 4, 5, 6, 1, 2, 11, 0, 9] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 7, 8, 3, 4, 5, 6, 1, 2, 11, 0, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row75Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row75Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row75Generator0, row75Generator1, row75Generator2]

abbrev Row75Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row75Generators)

noncomputable def row75Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row75Top

private def row76Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row76Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row76Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 9, 10, 7, 8, 5, 6, 3, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 9, 10, 7, 8, 5, 6, 3, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row76Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 0, 11, 10, 9, 5, 6, 7, 8, 4, 3, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 0, 11, 10, 9, 5, 6, 7, 8, 4, 3, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row76Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row76Generator0, row76Generator1, row76Generator2, row76Generator3]

abbrev Row76Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row76Generators)

noncomputable def row76Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row76Top

private def row77Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 2, 7, 4, 9, 6, 11, 8, 1, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 11, 4, 1, 6, 3, 8, 5, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row77Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row77Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row77Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row77Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row77Generator0, row77Generator1, row77Generator2, row77Generator3]

abbrev Row77Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row77Generators)

noncomputable def row77Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row77Top

private def row78Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row78Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row78Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 9, 10, 11, 0, 5, 6, 7, 8, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 11, 0, 1, 2, 7, 8, 9, 10, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row78Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 2, 1, 3, 4, 10, 9, 7, 8, 6, 5, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 2, 1, 3, 4, 10, 9, 7, 8, 6, 5, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row78Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row78Generator0, row78Generator1, row78Generator2, row78Generator3]

abbrev Row78Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row78Generators)

noncomputable def row78Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row78Top

private def row79Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 2, 7, 4, 9, 6, 11, 8, 1, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 11, 4, 1, 6, 3, 8, 5, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row79Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row79Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row79Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row79Generator0, row79Generator1, row79Generator2]

abbrev Row79Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row79Generators)

noncomputable def row79Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row79Top

private def row80Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row80Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 3, 4, 9, 10, 7, 8, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 3, 4, 1, 2, 7, 8, 5, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row80Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 11, 0, 5, 6, 7, 8, 9, 10, 3, 4, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[2, 11, 0, 9, 10, 3, 4, 5, 6, 7, 8, 1] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row80Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 2, 1, 3, 4, 10, 9, 7, 8, 6, 5, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 2, 1, 3, 4, 10, 9, 7, 8, 6, 5, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row80Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row80Generator0, row80Generator1, row80Generator2, row80Generator3]

abbrev Row80Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row80Generators)

noncomputable def row80Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row80Top

private def row81Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 2, 7, 4, 9, 6, 11, 8, 1, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 11, 4, 1, 6, 3, 8, 5, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row81Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row81Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row81Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row81Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row81Generator0, row81Generator1, row81Generator2, row81Generator3]

abbrev Row81Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row81Generators)

noncomputable def row81Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row81Top

private def row82Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 4, 3, 5, 6, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 4, 3, 5, 6, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row82Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 1, 2, 7, 8, 5, 6, 11, 0, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 1, 2, 11, 0, 5, 6, 3, 4, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row82Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row82Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 1, 2, 11, 0, 9, 10, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 3, 4, 9, 10, 11, 0, 1, 2, 7, 8, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row82Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row82Generator0, row82Generator1, row82Generator2, row82Generator3]

abbrev Row82Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row82Generators)

noncomputable def row82Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row82Top

private def row83Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row83Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 2, 3, 1, 8, 6, 7, 5, 0, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 2, 3, 1, 8, 6, 7, 5, 0, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row83Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row83Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row83Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row83Generator0, row83Generator1, row83Generator2, row83Generator3]

abbrev Row83Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row83Generators)

noncomputable def row83Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row83Top

private def row84Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 7, 4, 9, 10, 11, 8, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 11, 4, 1, 2, 3, 8, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row84Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row84Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 10, 8, 1, 7, 2, 0, 9, 11, 6, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 3, 5, 0, 10, 11, 9, 4, 2, 7, 1, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row84Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 3, 2, 4, 9, 11, 10, 8, 5, 7, 6] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 3, 2, 4, 9, 11, 10, 8, 5, 7, 6] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row84Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row84Generator0, row84Generator1, row84Generator2, row84Generator3]

abbrev Row84Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row84Generators)

noncomputable def row84Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row84Top

private def row85Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 1, 11, 6, 4, 8, 3, 7, 5, 0, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 1, 11, 6, 4, 8, 3, 7, 5, 0, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row85Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 4, 5, 3, 10, 8, 9, 7, 2, 0, 1, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 8, 3, 1, 2, 0, 7, 5, 6, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row85Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row85Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row85Generator0, row85Generator1, row85Generator2]

abbrev Row85Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row85Generators)

noncomputable def row85Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row85Top

private def row86Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row86Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row86Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row86Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row86Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row86Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row86Generator0, row86Generator1, row86Generator2, row86Generator3, row86Generator4]

abbrev Row86Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row86Generators)

noncomputable def row86Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row86Top

private def row87Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row87Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row87Generators : Fin 2 → Equiv.Perm (Fin 12) :=
  ![row87Generator0, row87Generator1]

abbrev Row87Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row87Generators)

noncomputable def row87Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row87Top

private def row88Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 3, 4, 6, 5, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 3, 4, 6, 5, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row88Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row88Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row88Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 9, 10, 5, 6, 7, 8, 3, 4, 11, 0, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 11, 0, 7, 8, 3, 4, 5, 6, 1, 2, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row88Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row88Generator0, row88Generator1, row88Generator2, row88Generator3]

abbrev Row88Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row88Generators)

noncomputable def row88Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row88Top

private def row89Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row89Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 3, 4, 9, 10, 7, 8, 1, 2, 11, 0, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 7, 8, 1, 2, 11, 0, 5, 6, 3, 4, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row89Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 5, 6, 3, 4, 7, 8, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 5, 6, 3, 4, 7, 8, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row89Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row89Generator0, row89Generator1, row89Generator2]

abbrev Row89Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row89Generators)

noncomputable def row89Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row89Top

private def row90Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row90Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row90Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row90Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row90Generator0, row90Generator1, row90Generator2]

abbrev Row90Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row90Generators)

noncomputable def row90Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row90Top

private def row91Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row91Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 3, 4, 9, 10, 7, 8, 1, 2, 11, 0, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 7, 8, 1, 2, 11, 0, 5, 6, 3, 4, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row91Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 3, 4, 6, 5, 9, 10, 8, 7, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 6, 5, 10, 9, 7, 8, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row91Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row91Generator0, row91Generator1, row91Generator2]

abbrev Row91Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row91Generators)

noncomputable def row91Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row91Top

private def row92Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 3, 4, 6, 5, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 3, 4, 6, 5, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row92Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row92Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row92Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 8, 9, 10, 6, 5, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 7, 8, 9, 10, 6, 5, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row92Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row92Generator0, row92Generator1, row92Generator2, row92Generator3]

abbrev Row92Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row92Generators)

noncomputable def row92Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row92Top

private def row93Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 3, 4, 6, 5, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 3, 4, 6, 5, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row93Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row93Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row93Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 8, 9, 10, 5, 6, 2, 1, 3, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 8, 7, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row93Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row93Generator0, row93Generator1, row93Generator2, row93Generator3]

abbrev Row93Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row93Generators)

noncomputable def row93Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row93Top

private def row94Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 3, 4, 8, 6, 7, 11, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 2, 6, 7, 5, 9, 10, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row94Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row94Generators : Fin 2 → Equiv.Perm (Fin 12) :=
  ![row94Generator0, row94Generator1]

abbrev Row94Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row94Generators)

noncomputable def row94Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row94Top

private def row95Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row95Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 1, 5, 0, 4, 8, 3, 7, 11, 6, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[3, 1, 11, 6, 4, 2, 9, 7, 5, 0, 10, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row95Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row95Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row95Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row95Generator0, row95Generator1, row95Generator2, row95Generator3]

abbrev Row95Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row95Generators)

noncomputable def row95Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row95Top

private def row96Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row96Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row96Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 2, 1, 9, 10, 7, 8, 5, 6, 3, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 2, 1, 9, 10, 7, 8, 5, 6, 3, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row96Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row96Generator0, row96Generator1, row96Generator2]

abbrev Row96Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row96Generators)

noncomputable def row96Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row96Top

private def row97Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row97Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row97Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 11, 0, 7, 8, 10, 9, 3, 4, 6, 5, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[2, 11, 0, 7, 8, 10, 9, 3, 4, 6, 5, 1] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row97Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row97Generator0, row97Generator1, row97Generator2]

abbrev Row97Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row97Generators)

noncomputable def row97Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row97Top

private def row98Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row98Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 1, 5, 0, 4, 8, 3, 7, 11, 6, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[3, 1, 11, 6, 4, 2, 9, 7, 5, 0, 10, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row98Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row98Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[7, 0, 5, 10, 3, 8, 1, 6, 11, 4, 9, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 6, 11, 4, 9, 2, 7, 0, 5, 10, 3, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row98Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row98Generator0, row98Generator1, row98Generator2, row98Generator3]

abbrev Row98Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row98Generators)

noncomputable def row98Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row98Top

private def row99Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row99Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row99Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 5, 6, 3, 4, 9, 10, 7, 8, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 5, 6, 3, 4, 9, 10, 7, 8, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row99Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 2, 1, 4, 3, 5, 6, 9, 10, 8, 7, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 2, 1, 4, 3, 5, 6, 10, 9, 7, 8, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row99Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row99Generator0, row99Generator1, row99Generator2, row99Generator3]

abbrev Row99Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row99Generators)

noncomputable def row99Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row99Top

private def row100Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row100Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row100Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 3, 4, 7, 8, 9, 10, 1, 2, 11, 0, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 7, 8, 1, 2, 11, 0, 3, 4, 5, 6, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row100Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 2, 1, 7, 8, 10, 9, 3, 4, 6, 5, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 2, 1, 7, 8, 10, 9, 3, 4, 6, 5, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row100Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row100Generator0, row100Generator1, row100Generator2, row100Generator3]

abbrev Row100Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row100Generators)

noncomputable def row100Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row100Top

private def row101Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row101Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 1, 11, 6, 4, 8, 3, 7, 5, 0, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 1, 11, 6, 4, 8, 3, 7, 5, 0, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row101Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row101Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row101Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row101Generator0, row101Generator1, row101Generator2, row101Generator3]

abbrev Row101Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row101Generators)

noncomputable def row101Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row101Top

private def row102Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row102Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row102Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 3, 4, 7, 8, 9, 10, 1, 2, 11, 0, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 7, 8, 1, 2, 11, 0, 3, 4, 5, 6, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row102Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 11, 0, 7, 8, 10, 9, 4, 3, 5, 6, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[2, 0, 11, 8, 7, 9, 10, 3, 4, 6, 5, 1] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row102Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row102Generator0, row102Generator1, row102Generator2, row102Generator3]

abbrev Row102Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row102Generators)

noncomputable def row102Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row102Top

private def row103Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row103Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 9, 4, 11, 0, 7, 2, 3, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 9, 4, 11, 0, 7, 2, 3, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row103Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row103Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 3, 8, 1, 6, 11, 4, 9, 2, 7, 0, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 3, 8, 1, 6, 11, 4, 9, 2, 7, 0, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row103Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row103Generator0, row103Generator1, row103Generator2, row103Generator3]

abbrev Row103Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row103Generators)

noncomputable def row103Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row103Top

private def row104Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row104Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row104Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 3, 4, 6, 5, 9, 10, 7, 8, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 6, 5, 9, 10, 7, 8, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row104Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row104Generator0, row104Generator1, row104Generator2]

abbrev Row104Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row104Generators)

noncomputable def row104Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row104Top

private def row105Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row105Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 0, 11, 1, 2, 3, 4, 5, 6, 7, 8, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row105Generators : Fin 2 → Equiv.Perm (Fin 12) :=
  ![row105Generator0, row105Generator1]

abbrev Row105Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row105Generators)

noncomputable def row105Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row105Top

private def row106Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row106Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row106Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 3, 4, 6, 5, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 3, 4, 6, 5, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row106Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row106Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 7, 8, 5, 6, 3, 4, 1, 2, 11, 0, 9] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 7, 8, 5, 6, 3, 4, 1, 2, 11, 0, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row106Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row106Generator0, row106Generator1, row106Generator2, row106Generator3, row106Generator4]

abbrev Row106Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row106Generators)

noncomputable def row106Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row106Top

private def row107Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row107Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row107Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 3, 4, 6, 5, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 3, 4, 6, 5, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row107Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row107Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 7, 8, 5, 6, 3, 4, 1, 2, 11, 0, 10] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 7, 8, 5, 6, 3, 4, 1, 2, 0, 11, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row107Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row107Generator0, row107Generator1, row107Generator2, row107Generator3, row107Generator4]

abbrev Row107Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row107Generators)

noncomputable def row107Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row107Top

private def row108Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row108Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 3, 4, 5, 6, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 3, 4, 5, 6, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row108Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row108Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 8, 7, 5, 6, 3, 4, 1, 2, 11, 0, 10] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 7, 8, 5, 6, 3, 4, 2, 1, 0, 11, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row108Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row108Generator0, row108Generator1, row108Generator2, row108Generator3]

abbrev Row108Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row108Generators)

noncomputable def row108Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row108Top

private def row109Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row109Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 3, 4, 5, 6, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 3, 4, 5, 6, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row109Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row109Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 7, 8, 5, 6, 3, 4, 1, 2, 11, 0, 9] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 7, 8, 5, 6, 3, 4, 1, 2, 11, 0, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row109Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row109Generator0, row109Generator1, row109Generator2, row109Generator3]

abbrev Row109Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row109Generators)

noncomputable def row109Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row109Top

private def row110Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 6, 5, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 6, 5, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row110Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row110Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row110Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row110Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row110Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row110Generator0, row110Generator1, row110Generator2, row110Generator3, row110Generator4]

abbrev Row110Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row110Generators)

noncomputable def row110Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row110Top

private def row111Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 6, 5, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 6, 5, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row111Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row111Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row111Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 9, 10, 5, 6, 7, 8, 3, 4, 11, 0, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 11, 0, 7, 8, 3, 4, 5, 6, 1, 2, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row111Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 3, 4, 1, 2, 6, 5, 10, 9, 8, 7, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 3, 4, 1, 2, 6, 5, 10, 9, 8, 7, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row111Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row111Generator0, row111Generator1, row111Generator2, row111Generator3, row111Generator4]

abbrev Row111Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row111Generators)

noncomputable def row111Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row111Top

private def row112Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 6, 5, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 6, 5, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row112Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row112Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 11, 0, 9, 10, 7, 8, 5, 6, 3, 4, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[2, 11, 0, 9, 10, 7, 8, 5, 6, 3, 4, 1] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row112Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 2, 1, 9, 10, 6, 5, 7, 8, 3, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 2, 1, 9, 10, 6, 5, 7, 8, 3, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row112Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row112Generator0, row112Generator1, row112Generator2, row112Generator3]

abbrev Row112Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row112Generators)

noncomputable def row112Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row112Top

private def row113Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 6, 5, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 6, 5, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row113Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row113Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 11, 0, 9, 10, 7, 8, 5, 6, 3, 4, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[2, 11, 0, 9, 10, 7, 8, 5, 6, 3, 4, 1] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row113Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 9, 10, 6, 5, 8, 7, 3, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 9, 10, 6, 5, 8, 7, 3, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row113Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row113Generator0, row113Generator1, row113Generator2, row113Generator3]

abbrev Row113Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row113Generators)

noncomputable def row113Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row113Top

private def row114Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 6, 5, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 6, 5, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row114Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row114Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row114Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row114Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 3, 4, 1, 2, 5, 6, 10, 9, 8, 7, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 3, 4, 1, 2, 5, 6, 10, 9, 8, 7, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row114Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row114Generator0, row114Generator1, row114Generator2, row114Generator3, row114Generator4]

abbrev Row114Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row114Generators)

noncomputable def row114Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row114Top

private def row115Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 6, 5, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 6, 5, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row115Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row115Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row115Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 3, 4, 1, 2, 6, 5, 9, 10, 7, 8, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 3, 4, 1, 2, 6, 5, 9, 10, 7, 8, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row115Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row115Generator0, row115Generator1, row115Generator2, row115Generator3]

abbrev Row115Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row115Generators)

noncomputable def row115Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row115Top

private def row116Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 7, 4, 9, 10, 11, 8, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 11, 4, 1, 2, 3, 8, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row116Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row116Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row116Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row116Generator0, row116Generator1, row116Generator2]

abbrev Row116Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row116Generators)

noncomputable def row116Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row116Top

private def row117Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 7, 4, 9, 10, 11, 8, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 11, 4, 1, 2, 3, 8, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row117Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row117Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row117Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row117Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row117Generator0, row117Generator1, row117Generator2, row117Generator3]

abbrev Row117Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row117Generators)

noncomputable def row117Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row117Top

private def row118Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 7, 4, 9, 10, 11, 8, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 11, 4, 1, 2, 3, 8, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row118Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row118Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row118Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row118Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row118Generator0, row118Generator1, row118Generator2, row118Generator3]

abbrev Row118Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row118Generators)

noncomputable def row118Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row118Top

private def row119Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 7, 4, 9, 10, 11, 8, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 11, 4, 1, 2, 3, 8, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row119Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row119Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row119Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row119Generator0, row119Generator1, row119Generator2]

abbrev Row119Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row119Generators)

noncomputable def row119Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row119Top

private def row120Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 7, 4, 9, 10, 11, 8, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 11, 4, 1, 2, 3, 8, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row120Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row120Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row120Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row120Generator0, row120Generator1, row120Generator2]

abbrev Row120Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row120Generators)

noncomputable def row120Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row120Top

private def row121Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 7, 4, 9, 10, 11, 8, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 11, 4, 1, 2, 3, 8, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row121Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 2, 9, 4, 11, 6, 1, 8, 3, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 7, 2, 9, 4, 11, 6, 1, 8, 3, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row121Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row121Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 0, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 0, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row121Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row121Generator0, row121Generator1, row121Generator2, row121Generator3]

abbrev Row121Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row121Generators)

noncomputable def row121Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row121Top

private def row122Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 7, 4, 9, 10, 11, 8, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 11, 4, 1, 2, 3, 8, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row122Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row122Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 2, 3, 1, 4, 6, 7, 5, 8, 10, 11, 9] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 3, 1, 2, 4, 7, 5, 6, 8, 11, 9, 10] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row122Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 0, 5, 3, 10, 8, 1, 7, 2, 4, 9, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 6, 8, 3, 9, 2, 0, 7, 5, 10, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row122Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row122Generator0, row122Generator1, row122Generator2, row122Generator3]

abbrev Row122Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row122Generators)

noncomputable def row122Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row122Top

private def row123Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 5, 6, 7, 8, 11, 0, 9, 10, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 11, 0, 1, 2, 3, 4, 5, 6, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row123Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 3, 4, 1, 2, 7, 8, 5, 6, 11, 0, 9] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 3, 4, 1, 2, 7, 8, 5, 6, 11, 0, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row123Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row123Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row123Generator0, row123Generator1, row123Generator2]

abbrev Row123Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row123Generators)

noncomputable def row123Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row123Top

private def row124Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row124Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row124Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 0, 11, 5, 6, 4, 3, 10, 9, 7, 8, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 11, 0, 6, 5, 3, 4, 9, 10, 8, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row124Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row124Generator0, row124Generator1, row124Generator2]

abbrev Row124Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row124Generators)

noncomputable def row124Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row124Top

private def row125Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 2, 7, 4, 9, 6, 11, 8, 1, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 11, 4, 1, 6, 3, 8, 5, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row125Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row125Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row125Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row125Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row125Generator0, row125Generator1, row125Generator2, row125Generator3]

abbrev Row125Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row125Generators)

noncomputable def row125Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row125Top

private def row126Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 2, 9, 4, 5, 6, 1, 8, 3, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 7, 2, 9, 4, 5, 6, 1, 8, 3, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row126Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 2, 7, 4, 9, 6, 11, 8, 1, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 11, 4, 1, 6, 3, 8, 5, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row126Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row126Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row126Generator0, row126Generator1, row126Generator2]

abbrev Row126Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row126Generators)

noncomputable def row126Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row126Top

private def row127Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 1, 11, 6, 4, 8, 3, 7, 5, 0, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 1, 11, 6, 4, 8, 3, 7, 5, 0, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row127Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 4, 5, 3, 10, 8, 9, 7, 2, 0, 1, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 8, 3, 1, 2, 0, 7, 5, 6, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row127Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row127Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 0, 2, 7, 9, 8, 10, 3, 5, 4, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 0, 2, 7, 9, 8, 10, 3, 5, 4, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row127Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row127Generator0, row127Generator1, row127Generator2, row127Generator3]

abbrev Row127Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row127Generators)

noncomputable def row127Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row127Top

private def row128Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 1, 11, 6, 4, 8, 3, 7, 5, 0, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 1, 11, 6, 4, 8, 3, 7, 5, 0, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row128Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 4, 5, 3, 10, 8, 9, 7, 2, 0, 1, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 8, 3, 1, 2, 0, 7, 5, 6, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row128Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row128Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row128Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row128Generator0, row128Generator1, row128Generator2, row128Generator3]

abbrev Row128Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row128Generators)

noncomputable def row128Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row128Top

private def row129Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 1, 11, 6, 4, 8, 3, 7, 5, 0, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 1, 11, 6, 4, 8, 3, 7, 5, 0, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row129Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 4, 5, 3, 10, 8, 9, 7, 2, 0, 1, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 8, 3, 1, 2, 0, 7, 5, 6, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row129Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 6, 4, 8, 3, 10, 5, 9, 7, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 6, 4, 8, 3, 10, 5, 9, 7, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row129Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row129Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row129Generator0, row129Generator1, row129Generator2, row129Generator3]

abbrev Row129Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row129Generators)

noncomputable def row129Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row129Top

private def row130Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row130Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row130Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row130Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row130Generator0, row130Generator1, row130Generator2]

abbrev Row130Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row130Generators)

noncomputable def row130Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row130Top

private def row131Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row131Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row131Generators : Fin 2 → Equiv.Perm (Fin 12) :=
  ![row131Generator0, row131Generator1]

abbrev Row131Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row131Generators)

noncomputable def row131Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row131Top

private def row132Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 7, 4, 9, 10, 11, 8, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 11, 4, 1, 2, 3, 8, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row132Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row132Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row132Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 4, 5, 7, 10, 8, 9, 11, 2, 0, 1, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 8, 11, 1, 2, 0, 3, 5, 6, 4, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row132Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row132Generator0, row132Generator1, row132Generator2, row132Generator3]

abbrev Row132Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row132Generators)

noncomputable def row132Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row132Top

private def row133Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 7, 4, 9, 10, 11, 8, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 11, 4, 1, 2, 3, 8, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row133Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 5, 6, 4, 11, 9, 10, 8, 3, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 10, 11, 9, 4, 2, 3, 1, 8, 6, 7, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row133Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 4, 5, 3, 10, 8, 9, 7, 2, 0, 1, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 8, 3, 1, 2, 0, 7, 5, 6, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row133Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row133Generator0, row133Generator1, row133Generator2]

abbrev Row133Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row133Generators)

noncomputable def row133Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row133Top

private def row134Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row134Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row134Generators : Fin 2 → Equiv.Perm (Fin 12) :=
  ![row134Generator0, row134Generator1]

abbrev Row134Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row134Generators)

noncomputable def row134Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row134Top

private def row135Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row135Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row135Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 7, 8, 5, 6, 3, 4, 1, 2, 11, 0, 9] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 7, 8, 5, 6, 3, 4, 1, 2, 11, 0, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row135Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row135Generator0, row135Generator1, row135Generator2]

abbrev Row135Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row135Generators)

noncomputable def row135Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row135Top

private def row136Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row136Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row136Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 7, 8, 5, 6, 3, 4, 1, 2, 11, 0, 9] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 7, 8, 5, 6, 3, 4, 1, 2, 11, 0, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row136Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row136Generator0, row136Generator1, row136Generator2]

abbrev Row136Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row136Generators)

noncomputable def row136Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row136Top

private def row137Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 3, 4, 6, 5, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 3, 4, 6, 5, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row137Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row137Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row137Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row137Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row137Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row137Generator0, row137Generator1, row137Generator2, row137Generator3, row137Generator4]

abbrev Row137Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row137Generators)

noncomputable def row137Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row137Top

private def row138Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row138Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 7, 8, 1, 2, 11, 0, 5, 6, 3, 4, 9] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 3, 4, 9, 10, 7, 8, 1, 2, 11, 0, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row138Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 8, 9, 10, 3, 4, 5, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 7, 8, 9, 10, 3, 4, 5, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row138Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 9, 10, 8, 7, 6, 5, 3, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 9, 10, 8, 7, 6, 5, 3, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row138Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row138Generator0, row138Generator1, row138Generator2, row138Generator3]

abbrev Row138Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row138Generators)

noncomputable def row138Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row138Top

private def row139Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row139Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row139Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row139Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row139Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row139Generator0, row139Generator1, row139Generator2, row139Generator3]

abbrev Row139Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row139Generators)

noncomputable def row139Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row139Top

private def row140Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 3, 4, 6, 5, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 3, 4, 6, 5, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row140Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row140Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row140Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row140Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 3, 4, 1, 2, 5, 6, 10, 9, 8, 7, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 3, 4, 1, 2, 5, 6, 10, 9, 8, 7, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row140Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row140Generator0, row140Generator1, row140Generator2, row140Generator3, row140Generator4]

abbrev Row140Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row140Generators)

noncomputable def row140Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row140Top

private def row141Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 3, 4, 8, 6, 7, 11, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 2, 6, 7, 5, 9, 10, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row141Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row141Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row141Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row141Generator0, row141Generator1, row141Generator2]

abbrev Row141Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row141Generators)

noncomputable def row141Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row141Top

private def row142Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row142Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row142Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row142Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row142Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row142Generator0, row142Generator1, row142Generator2, row142Generator3]

abbrev Row142Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row142Generators)

noncomputable def row142Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row142Top

private def row143Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 3, 4, 6, 5, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 3, 4, 6, 5, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row143Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row143Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row143Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 9, 10, 6, 5, 7, 8, 3, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 9, 10, 6, 5, 7, 8, 3, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row143Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row143Generator0, row143Generator1, row143Generator2, row143Generator3]

abbrev Row143Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row143Generators)

noncomputable def row143Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row143Top

private def row144Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row144Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row144Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row144Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row144Generator0, row144Generator1, row144Generator2]

abbrev Row144Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row144Generators)

noncomputable def row144Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row144Top

private def row145Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row145Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row145Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 7, 8, 5, 6, 3, 4, 1, 2, 11, 0, 10] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 7, 8, 5, 6, 3, 4, 1, 2, 0, 11, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row145Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row145Generator0, row145Generator1, row145Generator2]

abbrev Row145Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row145Generators)

noncomputable def row145Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row145Top

private def row146Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 3, 4, 6, 5, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 3, 4, 6, 5, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row146Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row146Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row146Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row146Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 9, 10, 7, 8, 11, 0, 3, 4, 1, 2, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 9, 10, 7, 8, 11, 0, 3, 4, 1, 2, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row146Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row146Generator0, row146Generator1, row146Generator2, row146Generator3, row146Generator4]

abbrev Row146Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row146Generators)

noncomputable def row146Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row146Top

private def row147Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row147Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 7, 8, 1, 2, 11, 0, 5, 6, 3, 4, 9] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 3, 4, 9, 10, 7, 8, 1, 2, 11, 0, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row147Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 2, 1, 9, 10, 7, 8, 5, 6, 3, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 2, 1, 9, 10, 7, 8, 5, 6, 3, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row147Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row147Generator0, row147Generator1, row147Generator2]

abbrev Row147Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row147Generators)

noncomputable def row147Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row147Top

private def row148Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row148Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row148Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row148Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row148Generator0, row148Generator1, row148Generator2]

abbrev Row148Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row148Generators)

noncomputable def row148Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row148Top

private def row149Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 3, 4, 6, 5, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 3, 4, 6, 5, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row149Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row149Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row149Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 11, 0, 9, 10, 7, 8, 5, 6, 3, 4, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[2, 11, 0, 9, 10, 7, 8, 5, 6, 3, 4, 1] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row149Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 8, 9, 10, 6, 5, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 7, 8, 9, 10, 6, 5, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row149Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row149Generator0, row149Generator1, row149Generator2, row149Generator3, row149Generator4]

abbrev Row149Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row149Generators)

noncomputable def row149Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row149Top

private def row150Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 3, 4, 8, 6, 7, 11, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 2, 6, 7, 5, 9, 10, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row150Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row150Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row150Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row150Generator0, row150Generator1, row150Generator2]

abbrev Row150Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row150Generators)

noncomputable def row150Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row150Top

private def row151Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 3, 4, 8, 6, 7, 11, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 2, 6, 7, 5, 9, 10, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row151Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row151Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row151Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row151Generator0, row151Generator1, row151Generator2]

abbrev Row151Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row151Generators)

noncomputable def row151Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row151Top

private def row152Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row152Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row152Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 8, 9, 10, 5, 6, 3, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 9, 10, 7, 8, 3, 4, 5, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row152Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 2, 1, 7, 8, 10, 9, 3, 4, 6, 5, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 2, 1, 7, 8, 10, 9, 3, 4, 6, 5, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row152Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row152Generator0, row152Generator1, row152Generator2, row152Generator3]

abbrev Row152Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row152Generators)

noncomputable def row152Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row152Top

private def row153Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row153Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row153Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 11, 0, 7, 8, 9, 10, 5, 6, 3, 4, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[2, 11, 0, 9, 10, 7, 8, 3, 4, 5, 6, 1] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row153Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 11, 0, 5, 6, 4, 3, 9, 10, 8, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[2, 0, 11, 6, 5, 3, 4, 10, 9, 7, 8, 1] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row153Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row153Generator0, row153Generator1, row153Generator2, row153Generator3]

abbrev Row153Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row153Generators)

noncomputable def row153Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row153Top

private def row154Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row154Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row154Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 11, 0, 9, 10, 7, 8, 5, 6, 3, 4, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[2, 11, 0, 9, 10, 7, 8, 5, 6, 3, 4, 1] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row154Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 2, 1, 7, 8, 9, 10, 3, 4, 5, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 2, 1, 7, 8, 9, 10, 3, 4, 5, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row154Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row154Generator0, row154Generator1, row154Generator2, row154Generator3]

abbrev Row154Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row154Generators)

noncomputable def row154Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row154Top

private def row155Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row155Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row155Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 8, 9, 10, 3, 4, 5, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 7, 8, 9, 10, 3, 4, 5, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row155Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 11, 0, 9, 10, 7, 8, 6, 5, 4, 3, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[2, 0, 11, 10, 9, 8, 7, 5, 6, 3, 4, 1] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row155Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row155Generator0, row155Generator1, row155Generator2, row155Generator3]

abbrev Row155Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row155Generators)

noncomputable def row155Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row155Top

private def row156Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 7, 4, 9, 10, 11, 8, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 11, 4, 1, 2, 3, 8, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row156Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row156Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row156Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row156Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row156Generator0, row156Generator1, row156Generator2, row156Generator3]

abbrev Row156Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row156Generators)

noncomputable def row156Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row156Top

private def row157Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 7, 4, 9, 10, 11, 8, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 11, 4, 1, 2, 3, 8, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row157Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row157Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 10, 8, 1, 7, 2, 0, 9, 11, 6, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 3, 5, 0, 10, 11, 9, 4, 2, 7, 1, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row157Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 2, 3, 1, 4, 6, 7, 5, 8, 10, 11, 9] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 3, 1, 2, 4, 7, 5, 6, 8, 11, 9, 10] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row157Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row157Generator0, row157Generator1, row157Generator2, row157Generator3]

abbrev Row157Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row157Generators)

noncomputable def row157Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row157Top

private def row158Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row158Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 1, 2, 7, 8, 5, 6, 11, 0, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 1, 2, 11, 0, 5, 6, 3, 4, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row158Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row158Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row158Generator0, row158Generator1, row158Generator2]

abbrev Row158Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row158Generators)

noncomputable def row158Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row158Top

private def row159Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row159Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 1, 2, 7, 8, 5, 6, 11, 0, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 1, 2, 11, 0, 5, 6, 3, 4, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row159Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 3, 4, 9, 10, 7, 8, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 3, 4, 1, 2, 7, 8, 5, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row159Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 11, 0, 9, 10, 7, 8, 6, 5, 4, 3, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[2, 0, 11, 10, 9, 8, 7, 5, 6, 3, 4, 1] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row159Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row159Generator0, row159Generator1, row159Generator2, row159Generator3]

abbrev Row159Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row159Generators)

noncomputable def row159Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row159Top

private def row160Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 2, 9, 4, 5, 6, 1, 8, 3, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 7, 2, 9, 4, 5, 6, 1, 8, 3, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row160Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 2, 7, 4, 9, 6, 11, 8, 1, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 11, 4, 1, 6, 3, 8, 5, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row160Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 9, 10, 7, 8, 11, 0, 3, 4, 1, 2, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 9, 10, 7, 8, 11, 0, 3, 4, 1, 2, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row160Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 10, 1, 8, 3, 0, 5, 4, 7, 2, 9, 6] : Array (Fin 12))[x.val]!
  invFun x := (#[5, 2, 9, 4, 7, 6, 11, 8, 3, 10, 1, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row160Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row160Generator0, row160Generator1, row160Generator2, row160Generator3]

abbrev Row160Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row160Generators)

noncomputable def row160Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row160Top

private def row161Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 2, 9, 4, 5, 6, 1, 8, 3, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 7, 2, 9, 4, 5, 6, 1, 8, 3, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row161Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 2, 7, 4, 9, 6, 11, 8, 1, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 11, 4, 1, 6, 3, 8, 5, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row161Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 9, 10, 7, 8, 11, 0, 3, 4, 1, 2, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 9, 10, 7, 8, 11, 0, 3, 4, 1, 2, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row161Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row161Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row161Generator0, row161Generator1, row161Generator2, row161Generator3]

abbrev Row161Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row161Generators)

noncomputable def row161Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row161Top

private def row162Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row162Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 3, 4, 5, 6, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 3, 4, 5, 6, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row162Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 1, 2, 7, 8, 5, 6, 11, 0, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 1, 2, 11, 0, 5, 6, 3, 4, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row162Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row162Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 1, 2, 11, 0, 9, 10, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 3, 4, 9, 10, 11, 0, 1, 2, 7, 8, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row162Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row162Generator0, row162Generator1, row162Generator2, row162Generator3, row162Generator4]

abbrev Row162Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row162Generators)

noncomputable def row162Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row162Top

private def row163Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row163Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 3, 4, 5, 6, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 3, 4, 5, 6, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row163Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 1, 2, 7, 8, 5, 6, 11, 0, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 1, 2, 11, 0, 5, 6, 3, 4, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row163Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row163Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row163Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row163Generator0, row163Generator1, row163Generator2, row163Generator3, row163Generator4]

abbrev Row163Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row163Generators)

noncomputable def row163Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row163Top

private def row164Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row164Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row164Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 5, 6, 4, 11, 9, 10, 8, 3, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 10, 11, 9, 4, 2, 3, 1, 8, 6, 7, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row164Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row164Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row164Generator0, row164Generator1, row164Generator2, row164Generator3]

abbrev Row164Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row164Generators)

noncomputable def row164Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row164Top

private def row165Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 1, 11, 6, 4, 8, 3, 7, 5, 0, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 1, 11, 6, 4, 8, 3, 7, 5, 0, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row165Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 4, 5, 3, 10, 8, 9, 7, 2, 0, 1, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 8, 3, 1, 2, 0, 7, 5, 6, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row165Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 6, 4, 8, 3, 10, 5, 9, 7, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 6, 4, 8, 3, 10, 5, 9, 7, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row165Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row165Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row165Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row165Generator0, row165Generator1, row165Generator2, row165Generator3, row165Generator4]

abbrev Row165Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row165Generators)

noncomputable def row165Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row165Top

private def row166Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row166Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row166Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 5, 6, 4, 11, 9, 10, 8, 3, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 10, 11, 9, 4, 2, 3, 1, 8, 6, 7, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row166Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 9, 10, 11, 0, 1, 5, 3, 4, 8, 6, 7] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 5, 0, 7, 8, 6, 10, 11, 9, 1, 2, 3] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row166Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row166Generator0, row166Generator1, row166Generator2, row166Generator3]

abbrev Row166Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row166Generators)

noncomputable def row166Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row166Top

private def row167Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row167Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row167Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row167Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row167Generator0, row167Generator1, row167Generator2]

abbrev Row167Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row167Generators)

noncomputable def row167Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row167Top

private def row168Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row168Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row168Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row168Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row168Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row168Generator0, row168Generator1, row168Generator2, row168Generator3]

abbrev Row168Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row168Generators)

noncomputable def row168Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row168Top

private def row169Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row169Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row169Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row169Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row169Generator0, row169Generator1, row169Generator2]

abbrev Row169Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row169Generators)

noncomputable def row169Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row169Top

private def row170Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row170Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row170Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row170Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row170Generator0, row170Generator1, row170Generator2]

abbrev Row170Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row170Generators)

noncomputable def row170Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row170Top

private def row171Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row171Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row171Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row171Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 1, 10, 11, 4, 9, 2, 3, 0, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 3, 8, 9, 6, 11, 0, 1, 2, 7, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row171Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row171Generator0, row171Generator1, row171Generator2, row171Generator3]

abbrev Row171Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row171Generators)

noncomputable def row171Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row171Top

private def row172Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row172Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row172Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row172Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 3, 8, 1, 10, 11, 0, 9, 2, 7, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 3, 8, 1, 10, 11, 0, 9, 2, 7, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row172Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row172Generator0, row172Generator1, row172Generator2, row172Generator3]

abbrev Row172Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row172Generators)

noncomputable def row172Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row172Top

private def row173Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row173Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row173Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 0, 5, 6, 7, 8, 9, 10, 11, 4, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 10, 11, 0, 9, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row173Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row173Generator0, row173Generator1, row173Generator2]

abbrev Row173Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row173Generators)

noncomputable def row173Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row173Top

private def row174Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row174Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row174Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 0, 11, 6, 1, 8, 7, 10, 5, 4, 3, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 4, 11, 10, 9, 8, 3, 6, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row174Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 1, 10, 11, 4, 9, 2, 3, 0, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 3, 8, 9, 6, 11, 0, 1, 2, 7, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row174Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row174Generator0, row174Generator1, row174Generator2, row174Generator3]

abbrev Row174Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row174Generators)

noncomputable def row174Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row174Top

private def row175Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 7, 4, 9, 10, 11, 8, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 11, 4, 1, 2, 3, 8, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row175Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row175Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 2, 3, 1, 8, 6, 7, 5, 0, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 2, 3, 1, 8, 6, 7, 5, 0, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row175Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row175Generator0, row175Generator1, row175Generator2]

abbrev Row175Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row175Generators)

noncomputable def row175Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row175Top

private def row176Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 7, 4, 9, 10, 11, 8, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 11, 4, 1, 2, 3, 8, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row176Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row176Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 5, 6, 4, 11, 9, 10, 8, 3, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 10, 11, 9, 4, 2, 3, 1, 8, 6, 7, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row176Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 4, 5, 3, 10, 8, 9, 7, 2, 0, 1, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 8, 3, 1, 2, 0, 7, 5, 6, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row176Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row176Generator0, row176Generator1, row176Generator2, row176Generator3]

abbrev Row176Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row176Generators)

noncomputable def row176Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row176Top

private def row177Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 7, 4, 9, 10, 11, 8, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 11, 4, 1, 2, 3, 8, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row177Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row177Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 7, 6, 8, 9, 3, 2, 4, 5, 11, 10] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 7, 6, 8, 9, 3, 2, 4, 5, 11, 10] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row177Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 6, 5, 7, 8, 2, 1, 3, 4, 10, 9, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 6, 5, 7, 8, 2, 1, 3, 4, 10, 9, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row177Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row177Generator0, row177Generator1, row177Generator2, row177Generator3]

abbrev Row177Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row177Generators)

noncomputable def row177Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row177Top

private def row178Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 7, 4, 9, 10, 11, 8, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 11, 4, 1, 2, 3, 8, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row178Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 5, 6, 4, 11, 9, 10, 8, 3, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 10, 11, 9, 4, 2, 3, 1, 8, 6, 7, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row178Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 4, 5, 3, 10, 8, 9, 7, 2, 0, 1, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 8, 3, 1, 2, 0, 7, 5, 6, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row178Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row178Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row178Generator0, row178Generator1, row178Generator2, row178Generator3]

abbrev Row178Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row178Generators)

noncomputable def row178Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row178Top

private def row179Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row179Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 6, 7, 1, 8, 2, 3, 5, 0, 11, 10] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 6, 7, 1, 8, 2, 3, 5, 0, 11, 10] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row179Generators : Fin 2 → Equiv.Perm (Fin 12) :=
  ![row179Generator0, row179Generator1]

abbrev Row179Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row179Generators)

noncomputable def row179Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row179Top

private def row180Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 11, 0, 5, 6, 7, 8, 9, 10, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 11, 0, 1, 2, 5, 6, 7, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row180Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row180Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row180Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row180Generator0, row180Generator1, row180Generator2]

abbrev Row180Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row180Generators)

noncomputable def row180Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row180Top

private def row181Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 11, 0, 5, 8, 7, 10, 9, 6, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 11, 0, 1, 2, 5, 10, 7, 6, 9, 8, 3] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row181Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 3, 8, 5, 0, 7, 2, 9, 4, 1, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 6, 1, 8, 3, 0, 5, 2, 7, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row181Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 3, 4, 1, 10, 9, 8, 5, 6, 7, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 4, 1, 2, 3, 8, 9, 10, 7, 6, 5, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row181Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row181Generator0, row181Generator1, row181Generator2]

abbrev Row181Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row181Generators)

noncomputable def row181Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row181Top

private def row182Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 11, 0, 5, 8, 7, 10, 9, 6, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 11, 0, 1, 2, 5, 10, 7, 6, 9, 8, 3] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row182Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 3, 8, 5, 0, 7, 2, 9, 4, 1, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 6, 1, 8, 3, 0, 5, 2, 7, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row182Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 10, 9, 8, 7, 6, 5, 4, 3, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 10, 9, 8, 7, 6, 5, 4, 3, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row182Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row182Generator0, row182Generator1, row182Generator2]

abbrev Row182Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row182Generators)

noncomputable def row182Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row182Top

private def row183Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 11, 0, 5, 6, 7, 8, 9, 10, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 11, 0, 1, 2, 5, 6, 7, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row183Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row183Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 10, 9, 8, 7, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 10, 9, 8, 7, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row183Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row183Generator0, row183Generator1, row183Generator2]

abbrev Row183Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row183Generators)

noncomputable def row183Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row183Top

private def row184Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row184Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row184Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row184Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row184Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row184Generator0, row184Generator1, row184Generator2, row184Generator3]

abbrev Row184Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row184Generators)

noncomputable def row184Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row184Top

private def row185Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 3, 4, 8, 6, 7, 11, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 2, 6, 7, 5, 9, 10, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row185Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row185Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row185Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row185Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row185Generator0, row185Generator1, row185Generator2, row185Generator3]

abbrev Row185Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row185Generators)

noncomputable def row185Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row185Top

private def row186Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row186Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row186Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row186Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row186Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row186Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row186Generator0, row186Generator1, row186Generator2, row186Generator3, row186Generator4]

abbrev Row186Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row186Generators)

noncomputable def row186Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row186Top

private def row187Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row187Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 2, 3, 4, 11, 0, 7, 8, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 2, 3, 4, 11, 0, 7, 8, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row187Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row187Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row187Generator0, row187Generator1, row187Generator2]

abbrev Row187Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row187Generators)

noncomputable def row187Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row187Top

private def row188Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row188Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row188Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row188Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row188Generator0, row188Generator1, row188Generator2]

abbrev Row188Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row188Generators)

noncomputable def row188Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row188Top

private def row189Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 3, 4, 8, 6, 7, 11, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 2, 6, 7, 5, 9, 10, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row189Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 3, 4, 5, 0, 7, 2, 9, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 3, 4, 5, 0, 7, 2, 9, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row189Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row189Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row189Generator0, row189Generator1, row189Generator2]

abbrev Row189Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row189Generators)

noncomputable def row189Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row189Top

private def row190Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row190Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row190Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row190Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row190Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row190Generator0, row190Generator1, row190Generator2, row190Generator3]

abbrev Row190Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row190Generators)

noncomputable def row190Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row190Top

private def row191Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row191Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row191Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row191Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 9, 10, 7, 8, 11, 0, 3, 4, 1, 2, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 9, 10, 7, 8, 11, 0, 3, 4, 1, 2, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row191Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row191Generator0, row191Generator1, row191Generator2, row191Generator3]

abbrev Row191Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row191Generators)

noncomputable def row191Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row191Top

private def row192Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row192Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row192Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row192Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[5, 9, 10, 7, 8, 11, 0, 3, 4, 1, 2, 6] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 9, 10, 7, 8, 0, 11, 3, 4, 1, 2, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row192Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row192Generator0, row192Generator1, row192Generator2, row192Generator3]

abbrev Row192Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row192Generators)

noncomputable def row192Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row192Top

private def row193Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row193Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row193Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 7, 8, 5, 6, 3, 4, 1, 2, 11, 0, 9] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 7, 8, 5, 6, 3, 4, 1, 2, 11, 0, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row193Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row193Generator0, row193Generator1, row193Generator2]

abbrev Row193Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row193Generators)

noncomputable def row193Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row193Top

private def row194Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row194Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 5, 6, 4, 11, 9, 10, 8, 3, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 10, 11, 9, 4, 2, 3, 1, 8, 6, 7, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row194Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 4, 5, 3, 10, 8, 9, 7, 2, 0, 1, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 8, 3, 1, 2, 0, 7, 5, 6, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row194Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row194Generator0, row194Generator1, row194Generator2]

abbrev Row194Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row194Generators)

noncomputable def row194Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row194Top

private def row195Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row195Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 1, 2, 7, 8, 5, 6, 11, 0, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 1, 2, 11, 0, 5, 6, 3, 4, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row195Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row195Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row195Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row195Generator0, row195Generator1, row195Generator2, row195Generator3]

abbrev Row195Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row195Generators)

noncomputable def row195Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row195Top

private def row196Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row196Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 1, 2, 7, 8, 5, 6, 11, 0, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 1, 2, 11, 0, 5, 6, 3, 4, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row196Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row196Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 2, 1, 7, 8, 9, 10, 3, 4, 5, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 2, 1, 7, 8, 9, 10, 3, 4, 5, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row196Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row196Generator0, row196Generator1, row196Generator2, row196Generator3]

abbrev Row196Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row196Generators)

noncomputable def row196Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row196Top

private def row197Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row197Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 1, 2, 7, 8, 5, 6, 11, 0, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 1, 2, 11, 0, 5, 6, 3, 4, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row197Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row197Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[5, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 6] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 7, 8, 9, 10, 0, 11, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row197Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row197Generator0, row197Generator1, row197Generator2, row197Generator3]

abbrev Row197Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row197Generators)

noncomputable def row197Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row197Top

private def row198Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row198Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 1, 2, 7, 8, 5, 6, 11, 0, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 1, 2, 11, 0, 5, 6, 3, 4, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row198Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row198Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[5, 7, 8, 1, 2, 11, 0, 9, 10, 3, 4, 6] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 3, 4, 9, 10, 0, 11, 1, 2, 7, 8, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row198Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row198Generator0, row198Generator1, row198Generator2, row198Generator3]

abbrev Row198Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row198Generators)

noncomputable def row198Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row198Top

private def row199Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row199Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 1, 2, 7, 8, 5, 6, 11, 0, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 1, 2, 11, 0, 5, 6, 3, 4, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row199Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row199Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 1, 2, 11, 0, 9, 10, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 3, 4, 9, 10, 11, 0, 1, 2, 7, 8, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row199Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row199Generator0, row199Generator1, row199Generator2, row199Generator3]

abbrev Row199Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row199Generators)

noncomputable def row199Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row199Top

private def row200Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 2, 9, 4, 5, 6, 1, 8, 3, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 7, 2, 9, 4, 5, 6, 1, 8, 3, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row200Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 2, 7, 4, 9, 6, 11, 8, 1, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 11, 4, 1, 6, 3, 8, 5, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row200Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 2, 7, 4, 11, 6, 3, 8, 1, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 7, 4, 11, 6, 3, 8, 1, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row200Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row200Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row200Generator0, row200Generator1, row200Generator2, row200Generator3]

abbrev Row200Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row200Generators)

noncomputable def row200Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row200Top

private def row201Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row201Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 3, 4, 5, 6, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 3, 4, 5, 6, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row201Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 9, 10, 11, 0, 5, 6, 7, 8, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 11, 0, 1, 2, 7, 8, 9, 10, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row201Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 3, 4, 9, 10, 7, 8, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 3, 4, 1, 2, 7, 8, 5, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row201Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 3, 4, 9, 10, 8, 7, 5, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 9, 10, 8, 7, 5, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row201Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row201Generator0, row201Generator1, row201Generator2, row201Generator3, row201Generator4]

abbrev Row201Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row201Generators)

noncomputable def row201Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row201Top

private def row202Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 4, 3, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row202Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 3, 4, 5, 6, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 3, 4, 5, 6, 8, 7, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row202Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 9, 10, 11, 0, 5, 6, 7, 8, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 11, 0, 1, 2, 7, 8, 9, 10, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row202Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 3, 4, 9, 10, 7, 8, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 3, 4, 1, 2, 7, 8, 5, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row202Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 7, 8, 1, 2, 3, 4, 9, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 5, 6, 7, 8, 1, 2, 3, 4, 9, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row202Generator5 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 2, 1, 3, 4, 9, 10, 8, 7, 5, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 2, 1, 3, 4, 9, 10, 8, 7, 5, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row202Generators : Fin 6 → Equiv.Perm (Fin 12) :=
  ![row202Generator0, row202Generator1, row202Generator2, row202Generator3, row202Generator4, row202Generator5]

abbrev Row202Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row202Generators)

noncomputable def row202Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row202Top

private def row203Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 2, 9, 4, 5, 6, 1, 8, 3, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 7, 2, 9, 4, 5, 6, 1, 8, 3, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row203Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 2, 7, 4, 9, 6, 11, 8, 1, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 11, 4, 1, 6, 3, 8, 5, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row203Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row203Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row203Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row203Generator0, row203Generator1, row203Generator2, row203Generator3]

abbrev Row203Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row203Generators)

noncomputable def row203Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row203Top

private def row204Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row204Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row204Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 5, 6, 4, 11, 9, 10, 8, 3, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 10, 11, 9, 4, 2, 3, 1, 8, 6, 7, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row204Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row204Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 0, 2, 7, 9, 8, 10, 3, 5, 4, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 0, 2, 7, 9, 8, 10, 3, 5, 4, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row204Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row204Generator0, row204Generator1, row204Generator2, row204Generator3, row204Generator4]

abbrev Row204Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row204Generators)

noncomputable def row204Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row204Top

private def row205Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row205Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row205Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 5, 6, 4, 11, 9, 10, 8, 3, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 10, 11, 9, 4, 2, 3, 1, 8, 6, 7, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row205Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 2, 3, 1, 8, 6, 7, 5, 0, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 2, 3, 1, 8, 6, 7, 5, 0, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row205Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row205Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row205Generator0, row205Generator1, row205Generator2, row205Generator3, row205Generator4]

abbrev Row205Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row205Generators)

noncomputable def row205Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row205Top

private def row206Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row206Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row206Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 5, 6, 4, 11, 9, 10, 8, 3, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 10, 11, 9, 4, 2, 3, 1, 8, 6, 7, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row206Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row206Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row206Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row206Generator0, row206Generator1, row206Generator2, row206Generator3, row206Generator4]

abbrev Row206Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row206Generators)

noncomputable def row206Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row206Top

private def row207Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row207Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row207Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 5, 6, 4, 11, 9, 10, 8, 3, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 10, 11, 9, 4, 2, 3, 1, 8, 6, 7, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row207Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 0, 2, 10, 6, 8, 4, 9, 5, 7, 3, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 0, 2, 10, 6, 8, 4, 9, 5, 7, 3, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row207Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 1, 0, 11, 4, 9, 8, 10, 6, 5, 7, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[2, 1, 0, 11, 4, 9, 8, 10, 6, 5, 7, 3] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row207Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row207Generator0, row207Generator1, row207Generator2, row207Generator3, row207Generator4]

abbrev Row207Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row207Generators)

noncomputable def row207Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row207Top

private def row208Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 3, 4, 11, 6, 7, 8, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 11, 6, 7, 8, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row208Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 2, 7, 4, 9, 6, 11, 8, 1, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 11, 4, 1, 6, 3, 8, 5, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row208Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row208Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row208Generator0, row208Generator1, row208Generator2]

abbrev Row208Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row208Generators)

noncomputable def row208Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row208Top

private def row209Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row209Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row209Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row209Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 9, 8, 7, 10, 5, 0, 3, 2, 1, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 9, 8, 7, 10, 5, 0, 3, 2, 1, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row209Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row209Generator0, row209Generator1, row209Generator2, row209Generator3]

abbrev Row209Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row209Generators)

noncomputable def row209Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row209Top

private def row210Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row210Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row210Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row210Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row210Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row210Generator0, row210Generator1, row210Generator2, row210Generator3]

abbrev Row210Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row210Generators)

noncomputable def row210Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row210Top

private def row211Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row211Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row211Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row211Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row211Generator0, row211Generator1, row211Generator2]

abbrev Row211Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row211Generators)

noncomputable def row211Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row211Top

private def row212Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row212Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row212Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 4, 11, 6, 9, 8, 7, 10, 5, 0, 3, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 0, 11, 10, 1, 8, 3, 6, 5, 4, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row212Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 2, 1, 3, 8, 10, 9, 7, 4, 6, 5, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 2, 1, 3, 8, 10, 9, 7, 4, 6, 5, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row212Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row212Generator0, row212Generator1, row212Generator2, row212Generator3]

abbrev Row212Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row212Generators)

noncomputable def row212Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row212Top

private def row213Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 7, 4, 9, 10, 11, 8, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 11, 4, 1, 2, 3, 8, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row213Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row213Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row213Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 2, 3, 1, 8, 6, 7, 5, 0, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 2, 3, 1, 8, 6, 7, 5, 0, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row213Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row213Generator0, row213Generator1, row213Generator2, row213Generator3]

abbrev Row213Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row213Generators)

noncomputable def row213Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row213Top

private def row214Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row214Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row214Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 1, 2, 11, 0, 9, 10, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 3, 4, 9, 10, 11, 0, 1, 2, 7, 8, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row214Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row214Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row214Generator0, row214Generator1, row214Generator2, row214Generator3]

abbrev Row214Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row214Generators)

noncomputable def row214Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row214Top

private def row215Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row215Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row215Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 1, 2, 11, 0, 9, 10, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 3, 4, 9, 10, 11, 0, 1, 2, 7, 8, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row215Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 8, 1, 2, 3, 0, 5, 10, 7, 4, 9, 6] : Array (Fin 12))[x.val]!
  invFun x := (#[5, 2, 3, 4, 9, 6, 11, 8, 1, 10, 7, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row215Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row215Generator0, row215Generator1, row215Generator2, row215Generator3]

abbrev Row215Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row215Generators)

noncomputable def row215Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row215Top

private def row216Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row216Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row216Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row216Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 2, 1, 3, 8, 10, 9, 7, 4, 6, 5, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 2, 1, 3, 8, 10, 9, 7, 4, 6, 5, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row216Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row216Generator0, row216Generator1, row216Generator2, row216Generator3]

abbrev Row216Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row216Generators)

noncomputable def row216Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row216Top

private def row217Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row217Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row217Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row217Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row217Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row217Generator0, row217Generator1, row217Generator2, row217Generator3]

abbrev Row217Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row217Generators)

noncomputable def row217Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row217Top

private def row218Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row218Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 6, 7, 1, 8, 2, 3, 5, 0, 11, 10] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 6, 7, 1, 8, 2, 3, 5, 0, 11, 10] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row218Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 3, 5, 7, 9, 0, 2, 4, 6, 8, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[5, 0, 6, 1, 7, 2, 8, 3, 9, 4, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row218Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row218Generator0, row218Generator1, row218Generator2]

abbrev Row218Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row218Generators)

noncomputable def row218Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row218Top

private def row219Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 11, 0, 3, 4, 5, 6, 7, 8, 9, 10, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[2, 11, 0, 3, 4, 5, 6, 7, 8, 9, 10, 1] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row219Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row219Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row219Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row219Generator0, row219Generator1, row219Generator2]

abbrev Row219Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row219Generators)

noncomputable def row219Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row219Top

private def row220Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 11, 0, 5, 8, 7, 10, 9, 6, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 11, 0, 1, 2, 5, 10, 7, 6, 9, 8, 3] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row220Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 3, 8, 5, 0, 7, 2, 9, 4, 1, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 6, 1, 8, 3, 0, 5, 2, 7, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row220Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[8, 11, 6, 3, 10, 5, 2, 7, 0, 9, 4, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 11, 6, 3, 10, 5, 2, 7, 0, 9, 4, 1] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row220Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 10, 9, 8, 7, 6, 5, 4, 3, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 10, 9, 8, 7, 6, 5, 4, 3, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row220Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row220Generator0, row220Generator1, row220Generator2, row220Generator3]

abbrev Row220Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row220Generators)

noncomputable def row220Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row220Top

private def row221Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 3, 4, 8, 6, 7, 11, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 2, 6, 7, 5, 9, 10, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row221Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 3, 4, 5, 0, 7, 2, 9, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 3, 4, 5, 0, 7, 2, 9, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row221Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row221Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row221Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row221Generator0, row221Generator1, row221Generator2, row221Generator3]

abbrev Row221Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row221Generators)

noncomputable def row221Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row221Top

private def row222Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 3, 4, 8, 6, 7, 11, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 2, 6, 7, 5, 9, 10, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row222Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 5, 6, 7, 2, 9, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 5, 6, 7, 2, 9, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row222Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row222Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row222Generator0, row222Generator1, row222Generator2]

abbrev Row222Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row222Generators)

noncomputable def row222Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row222Top

private def row223Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row223Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row223Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 3, 4, 5, 0, 7, 2, 9, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 3, 4, 5, 0, 7, 2, 9, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row223Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row223Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row223Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row223Generator0, row223Generator1, row223Generator2, row223Generator3, row223Generator4]

abbrev Row223Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row223Generators)

noncomputable def row223Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row223Top

private def row224Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row224Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row224Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row224Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 9, 10, 7, 8, 11, 0, 3, 4, 1, 2, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 9, 10, 7, 8, 11, 0, 3, 4, 1, 2, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row224Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row224Generator0, row224Generator1, row224Generator2, row224Generator3]

abbrev Row224Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row224Generators)

noncomputable def row224Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row224Top

private def row225Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 3, 4, 8, 6, 7, 11, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 2, 6, 7, 5, 9, 10, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row225Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 3, 4, 5, 0, 7, 2, 9, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 3, 4, 5, 0, 7, 2, 9, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row225Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row225Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row225Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row225Generator0, row225Generator1, row225Generator2, row225Generator3]

abbrev Row225Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row225Generators)

noncomputable def row225Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row225Top

private def row226Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row226Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 2, 3, 4, 11, 0, 7, 8, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 2, 3, 4, 11, 0, 7, 8, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row226Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row226Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row226Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row226Generator0, row226Generator1, row226Generator2, row226Generator3]

abbrev Row226Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row226Generators)

noncomputable def row226Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row226Top

private def row227Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row227Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 7, 8, 9, 10, 5, 6, 1, 2, 3, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row227Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row227Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row227Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row227Generator0, row227Generator1, row227Generator2, row227Generator3]

abbrev Row227Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row227Generators)

noncomputable def row227Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row227Top

private def row228Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row228Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row228Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 9, 4, 11, 3, 7, 8, 6, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 6, 4, 2, 9, 7, 8, 3, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row228Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 9, 7, 8, 3, 10, 11, 0, 1, 2, 6] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 5, 0, 1, 11, 3, 4, 2, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row228Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row228Generator0, row228Generator1, row228Generator2, row228Generator3]

abbrev Row228Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row228Generators)

noncomputable def row228Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row228Top

private def row229Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row229Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row229Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 9, 4, 11, 3, 7, 8, 6, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 6, 4, 2, 9, 7, 8, 3, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row229Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row229Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row229Generator0, row229Generator1, row229Generator2, row229Generator3]

abbrev Row229Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row229Generators)

noncomputable def row229Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row229Top

private def row230Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row230Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 5, 6, 7, 8, 11, 0, 9, 10, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 11, 0, 1, 2, 3, 4, 5, 6, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row230Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 7, 8, 3, 4, 5, 6, 1, 2, 11, 0, 9] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 7, 8, 3, 4, 5, 6, 1, 2, 11, 0, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row230Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row230Generator0, row230Generator1, row230Generator2]

abbrev Row230Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row230Generators)

noncomputable def row230Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row230Top

private def row231Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row231Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row231Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 2, 3, 1, 8, 6, 7, 5, 0, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 2, 3, 1, 8, 6, 7, 5, 0, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row231Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row231Generator0, row231Generator1, row231Generator2]

abbrev Row231Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row231Generators)

noncomputable def row231Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row231Top

private def row232Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row232Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row232Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 4, 5, 3, 10, 8, 9, 7, 2, 0, 1, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 8, 3, 1, 2, 0, 7, 5, 6, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row232Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 5, 10, 4, 11, 1, 6, 8, 3, 9, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 6, 11, 9, 4, 2, 7, 1, 8, 10, 3, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row232Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row232Generator0, row232Generator1, row232Generator2, row232Generator3]

abbrev Row232Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row232Generators)

noncomputable def row232Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row232Top

private def row233Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row233Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 5, 6, 4, 11, 9, 10, 8, 3, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 10, 11, 9, 4, 2, 3, 1, 8, 6, 7, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row233Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 4, 5, 3, 10, 8, 9, 7, 2, 0, 1, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 8, 3, 1, 2, 0, 7, 5, 6, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row233Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row233Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row233Generator0, row233Generator1, row233Generator2, row233Generator3]

abbrev Row233Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row233Generators)

noncomputable def row233Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row233Top

private def row234Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row234Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row234Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 5, 6, 4, 11, 9, 10, 8, 3, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 10, 11, 9, 4, 2, 3, 1, 8, 6, 7, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row234Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 4, 5, 3, 10, 8, 9, 7, 2, 0, 1, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 8, 3, 1, 2, 0, 7, 5, 6, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row234Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row234Generator0, row234Generator1, row234Generator2, row234Generator3]

abbrev Row234Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row234Generators)

noncomputable def row234Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row234Top

private def row235Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row235Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 3, 4, 9, 10, 7, 8, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 3, 4, 1, 2, 7, 8, 5, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row235Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row235Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 7, 8, 1, 2, 3, 4, 9, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 5, 6, 7, 8, 1, 2, 3, 4, 9, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row235Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 3, 4, 9, 10, 8, 7, 5, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 9, 10, 8, 7, 5, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row235Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row235Generator0, row235Generator1, row235Generator2, row235Generator3, row235Generator4]

abbrev Row235Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row235Generators)

noncomputable def row235Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row235Top

private def row236Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row236Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 1, 2, 7, 8, 5, 6, 11, 0, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 1, 2, 11, 0, 5, 6, 3, 4, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row236Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 8, 5, 6, 3, 4, 9, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 7, 8, 5, 6, 3, 4, 9, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row236Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row236Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row236Generator0, row236Generator1, row236Generator2, row236Generator3]

abbrev Row236Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row236Generators)

noncomputable def row236Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row236Top

private def row237Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row237Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 3, 4, 9, 10, 7, 8, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 3, 4, 1, 2, 7, 8, 5, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row237Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 8, 5, 6, 3, 4, 9, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 7, 8, 5, 6, 3, 4, 9, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row237Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 3, 4, 5, 6, 11, 0, 9, 10, 8, 7, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 11, 0, 1, 2, 3, 4, 10, 9, 7, 8, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row237Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row237Generator0, row237Generator1, row237Generator2, row237Generator3]

abbrev Row237Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row237Generators)

noncomputable def row237Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row237Top

private def row238Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row238Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 5, 6, 3, 4, 9, 10, 7, 8, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 3, 4, 1, 2, 7, 8, 5, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row238Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[2, 11, 0, 5, 6, 7, 8, 9, 10, 3, 4, 1] : Array (Fin 12))[x.val]!
  invFun x := (#[2, 11, 0, 9, 10, 3, 4, 5, 6, 7, 8, 1] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row238Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 3, 4, 9, 10, 8, 7, 5, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 9, 10, 8, 7, 5, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row238Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row238Generator0, row238Generator1, row238Generator2, row238Generator3]

abbrev Row238Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row238Generators)

noncomputable def row238Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row238Top

private def row239Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row239Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 11, 6, 7, 2, 9, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row239Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 5, 6, 4, 11, 9, 10, 8, 3, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 10, 11, 9, 4, 2, 3, 1, 8, 6, 7, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row239Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 2, 3, 1, 8, 6, 7, 5, 0, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 2, 3, 1, 8, 6, 7, 5, 0, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row239Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row239Generator5 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row239Generators : Fin 6 → Equiv.Perm (Fin 12) :=
  ![row239Generator0, row239Generator1, row239Generator2, row239Generator3, row239Generator4, row239Generator5]

abbrev Row239Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row239Generators)

noncomputable def row239Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row239Top

private def row240Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row240Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 1, 2, 7, 8, 5, 6, 11, 0, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 1, 2, 11, 0, 5, 6, 3, 4, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row240Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row240Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row240Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row240Generator0, row240Generator1, row240Generator2, row240Generator3]

abbrev Row240Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row240Generators)

noncomputable def row240Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row240Top

private def row241Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row241Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 1, 2, 7, 8, 5, 6, 11, 0, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 1, 2, 11, 0, 5, 6, 3, 4, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row241Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row241Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 1, 2, 11, 0, 9, 10, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 3, 4, 9, 10, 11, 0, 1, 2, 7, 8, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row241Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row241Generator0, row241Generator1, row241Generator2, row241Generator3]

abbrev Row241Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row241Generators)

noncomputable def row241Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row241Top

private def row242Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row242Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 10, 3, 8, 9, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 7, 4, 5, 10, 3, 8, 9, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row242Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row242Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row242Generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row242Generators : Fin 5 → Equiv.Perm (Fin 12) :=
  ![row242Generator0, row242Generator1, row242Generator2, row242Generator3, row242Generator4]

abbrev Row242Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row242Generators)

noncomputable def row242Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row242Top

private def row243Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row243Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row243Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row243Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 3, 10, 9, 0, 7, 2, 5, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 3, 10, 9, 0, 7, 2, 5, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row243Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row243Generator0, row243Generator1, row243Generator2, row243Generator3]

abbrev Row243Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row243Generators)

noncomputable def row243Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row243Top

private def row244Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row244Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row244Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row244Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 0, 5, 10, 7, 8, 1, 6, 11, 4, 9, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 6, 11, 0, 9, 2, 7, 4, 5, 10, 3, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row244Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row244Generator0, row244Generator1, row244Generator2, row244Generator3]

abbrev Row244Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row244Generators)

noncomputable def row244Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row244Top

private def row245Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row245Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 10, 3, 8, 9, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 7, 4, 5, 10, 3, 8, 9, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row245Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row245Generators : Fin 3 → Equiv.Perm (Fin 12) :=
  ![row245Generator0, row245Generator1, row245Generator2]

abbrev Row245Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row245Generators)

noncomputable def row245Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row245Top

private def row246Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row246Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row246Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 4, 11, 6, 1, 8, 3, 10, 5, 0, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row246Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 7, 8, 1, 10, 11, 0, 9, 2, 3, 4, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 3, 8, 9, 10, 11, 0, 1, 2, 7, 4, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row246Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row246Generator0, row246Generator1, row246Generator2, row246Generator3]

abbrev Row246Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row246Generators)

noncomputable def row246Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row246Top

private def row247Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row247Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row247Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row247Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[1, 0, 11, 6, 9, 8, 3, 10, 5, 4, 7, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[1, 0, 11, 6, 9, 8, 3, 10, 5, 4, 7, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row247Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row247Generator0, row247Generator1, row247Generator2, row247Generator3]

abbrev Row247Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row247Generators)

noncomputable def row247Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row247Top

private def row248Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row248Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row248Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row248Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[6, 1, 8, 3, 10, 5, 0, 7, 2, 9, 4, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row248Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row248Generator0, row248Generator1, row248Generator2, row248Generator3]

abbrev Row248Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row248Generators)

noncomputable def row248Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row248Top

private def row249Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 2, 11, 4, 5, 6, 3, 8, 9, 10, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row249Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 9, 2, 7, 4, 5, 6, 3, 8, 1, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row249Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 7, 2, 1, 4, 11, 6, 9, 8, 3, 10, 5] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 3, 2, 9, 4, 11, 6, 1, 8, 7, 10, 5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row249Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  invFun x := (#[11, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 0] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row249Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row249Generator0, row249Generator1, row249Generator2, row249Generator3]

abbrev Row249Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row249Generators)

noncomputable def row249Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row249Top

private def row250Generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 5, 3, 4, 8, 6, 7, 11, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 2, 6, 7, 5, 9, 10, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row250Generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 8, 3, 4, 5, 6, 7, 2, 9, 10, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 8, 3, 4, 5, 6, 7, 2, 9, 10, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row250Generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row250Generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  invFun x := (#[4, 9, 2, 7, 0, 5, 10, 3, 8, 1, 6, 11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row250Generators : Fin 4 → Equiv.Perm (Fin 12) :=
  ![row250Generator0, row250Generator1, row250Generator2, row250Generator3]

abbrev Row250Top : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range row250Generators)

noncomputable def row250Interface : DegreeTwoPairTopFiniteInterface 12 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row250Top

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

private def pairedSix1Generator0 : Equiv.Perm (Fin 6) where
  toFun x := (#[1, 3, 2, 0, 4, 5] : Array (Fin 6))[x.val]!
  invFun x := (#[3, 0, 2, 1, 4, 5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairedSix1Generator1 : Equiv.Perm (Fin 6) where
  toFun x := (#[0, 3, 2, 1, 5, 4] : Array (Fin 6))[x.val]!
  invFun x := (#[0, 3, 2, 1, 5, 4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairedSix1Generator2 : Equiv.Perm (Fin 6) where
  toFun x := (#[2, 4, 0, 5, 1, 3] : Array (Fin 6))[x.val]!
  invFun x := (#[2, 4, 0, 5, 1, 3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pairedSix1Generators : Fin 3 → Equiv.Perm (Fin 6) :=
  ![pairedSix1Generator0, pairedSix1Generator1, pairedSix1Generator2]

abbrev PairedSix1Top : Subgroup (Equiv.Perm (Fin 6)) :=
  Subgroup.closure (Set.range pairedSix1Generators)

noncomputable def pairedSix1Interface : DegreeTwoPairTopFiniteInterface 6 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    PairedSix1Top

private def pairedSix2Generator0 : Equiv.Perm (Fin 6) where
  toFun x := (#[1, 3, 2, 0, 4, 5] : Array (Fin 6))[x.val]!
  invFun x := (#[3, 0, 2, 1, 4, 5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairedSix2Generator1 : Equiv.Perm (Fin 6) where
  toFun x := (#[0, 3, 2, 1, 4, 5] : Array (Fin 6))[x.val]!
  invFun x := (#[0, 3, 2, 1, 4, 5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairedSix2Generator2 : Equiv.Perm (Fin 6) where
  toFun x := (#[2, 4, 0, 5, 1, 3] : Array (Fin 6))[x.val]!
  invFun x := (#[2, 4, 0, 5, 1, 3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pairedSix2Generators : Fin 3 → Equiv.Perm (Fin 6) :=
  ![pairedSix2Generator0, pairedSix2Generator1, pairedSix2Generator2]

abbrev PairedSix2Top : Subgroup (Equiv.Perm (Fin 6)) :=
  Subgroup.closure (Set.range pairedSix2Generators)

noncomputable def pairedSix2Interface : DegreeTwoPairTopFiniteInterface 6 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    PairedSix2Top

def branch : Fin 301 → DegreeTwoTwelvePairTopBranch :=
  Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .core <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .core <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .ternary <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .core <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .ternary <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .ternary <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .core <| Fin.cases .core <| Fin.cases .core <| Fin.cases .core <| Fin.cases .core <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .ternary <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .paired <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .ternary <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .ternary <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .paired <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .ternary <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .ternary <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.cases .joint <| Fin.elim0

def kappa : Fin 301 → ℕ :=
  Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 3 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 3 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 3 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 3 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 3 <| Fin.cases 3 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 3 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 3 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 3 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 3 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 3 <| Fin.cases 3 <| Fin.cases 3 <| Fin.cases 3 <| Fin.cases 3 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 3 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 3 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 3 <| Fin.cases 3 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 3 <| Fin.cases 2 <| Fin.cases 3 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 3 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 3 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 3 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 3 <| Fin.cases 3 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 3 <| Fin.cases 2 <| Fin.cases 4 <| Fin.cases 3 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 3 <| Fin.cases 2 <| Fin.cases 3 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 3 <| Fin.cases 3 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 3 <| Fin.cases 3 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 3 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.elim0

def sectionCap : Fin 301 → ℕ :=
  Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 3 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 3 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 3 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 2 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.cases 1 <| Fin.elim0

/-- Every generated joint row uses one of the six certified
`(kappa, sectionCap)` pairs. -/
theorem joint_parameters (j : Fin 301) (h : branch j = .joint) :
    (kappa j, sectionCap j) ∈ degreeTwoTwelvePairJointParameters := by
  revert h
  native_decide +revert

noncomputable def finiteInterface : Fin 301 →
    DegreeTwoPairTopFiniteInterface 12 :=
  Fin.cases row1Interface <| Fin.cases row2Interface <| Fin.cases row3Interface <| Fin.cases row4Interface <| Fin.cases row5Interface <| Fin.cases row6Interface <| Fin.cases row7Interface <| Fin.cases row8Interface <| Fin.cases row9Interface <| Fin.cases row10Interface <| Fin.cases row11Interface <| Fin.cases row12Interface <| Fin.cases row13Interface <| Fin.cases row14Interface <| Fin.cases row15Interface <| Fin.cases row16Interface <| Fin.cases row17Interface <| Fin.cases row18Interface <| Fin.cases row19Interface <| Fin.cases row20Interface <| Fin.cases row21Interface <| Fin.cases row22Interface <| Fin.cases row23Interface <| Fin.cases row24Interface <| Fin.cases row25Interface <| Fin.cases row26Interface <| Fin.cases row27Interface <| Fin.cases row28Interface <| Fin.cases row29Interface <| Fin.cases row30Interface <| Fin.cases row31Interface <| Fin.cases row32Interface <| Fin.cases row33Interface <| Fin.cases row34Interface <| Fin.cases row35Interface <| Fin.cases row36Interface <| Fin.cases row37Interface <| Fin.cases row38Interface <| Fin.cases row39Interface <| Fin.cases row40Interface <| Fin.cases row41Interface <| Fin.cases row42Interface <| Fin.cases row43Interface <| Fin.cases row44Interface <| Fin.cases row45Interface <| Fin.cases row46Interface <| Fin.cases row47Interface <| Fin.cases row48Interface <| Fin.cases row49Interface <| Fin.cases row50Interface <| Fin.cases row51Interface <| Fin.cases row52Interface <| Fin.cases row53Interface <| Fin.cases row54Interface <| Fin.cases row55Interface <| Fin.cases row56Interface <| Fin.cases row57Interface <| Fin.cases row58Interface <| Fin.cases row59Interface <| Fin.cases row60Interface <| Fin.cases row61Interface <| Fin.cases row62Interface <| Fin.cases row63Interface <| Fin.cases row64Interface <| Fin.cases row65Interface <| Fin.cases row66Interface <| Fin.cases row67Interface <| Fin.cases row68Interface <| Fin.cases row69Interface <| Fin.cases row70Interface <| Fin.cases row71Interface <| Fin.cases row72Interface <| Fin.cases row73Interface <| Fin.cases row74Interface <| Fin.cases row75Interface <| Fin.cases row76Interface <| Fin.cases row77Interface <| Fin.cases row78Interface <| Fin.cases row79Interface <| Fin.cases row80Interface <| Fin.cases row81Interface <| Fin.cases row82Interface <| Fin.cases row83Interface <| Fin.cases row84Interface <| Fin.cases row85Interface <| Fin.cases row86Interface <| Fin.cases row87Interface <| Fin.cases row88Interface <| Fin.cases row89Interface <| Fin.cases row90Interface <| Fin.cases row91Interface <| Fin.cases row92Interface <| Fin.cases row93Interface <| Fin.cases row94Interface <| Fin.cases row95Interface <| Fin.cases row96Interface <| Fin.cases row97Interface <| Fin.cases row98Interface <| Fin.cases row99Interface <| Fin.cases row100Interface <| Fin.cases row101Interface <| Fin.cases row102Interface <| Fin.cases row103Interface <| Fin.cases row104Interface <| Fin.cases row105Interface <| Fin.cases row106Interface <| Fin.cases row107Interface <| Fin.cases row108Interface <| Fin.cases row109Interface <| Fin.cases row110Interface <| Fin.cases row111Interface <| Fin.cases row112Interface <| Fin.cases row113Interface <| Fin.cases row114Interface <| Fin.cases row115Interface <| Fin.cases row116Interface <| Fin.cases row117Interface <| Fin.cases row118Interface <| Fin.cases row119Interface <| Fin.cases row120Interface <| Fin.cases row121Interface <| Fin.cases row122Interface <| Fin.cases row123Interface <| Fin.cases row124Interface <| Fin.cases row125Interface <| Fin.cases row126Interface <| Fin.cases row127Interface <| Fin.cases row128Interface <| Fin.cases row129Interface <| Fin.cases row130Interface <| Fin.cases row131Interface <| Fin.cases row132Interface <| Fin.cases row133Interface <| Fin.cases row134Interface <| Fin.cases row135Interface <| Fin.cases row136Interface <| Fin.cases row137Interface <| Fin.cases row138Interface <| Fin.cases row139Interface <| Fin.cases row140Interface <| Fin.cases row141Interface <| Fin.cases row142Interface <| Fin.cases row143Interface <| Fin.cases row144Interface <| Fin.cases row145Interface <| Fin.cases row146Interface <| Fin.cases row147Interface <| Fin.cases row148Interface <| Fin.cases row149Interface <| Fin.cases row150Interface <| Fin.cases row151Interface <| Fin.cases row152Interface <| Fin.cases row153Interface <| Fin.cases row154Interface <| Fin.cases row155Interface <| Fin.cases row156Interface <| Fin.cases row157Interface <| Fin.cases row158Interface <| Fin.cases row159Interface <| Fin.cases row160Interface <| Fin.cases row161Interface <| Fin.cases row162Interface <| Fin.cases row163Interface <| Fin.cases row164Interface <| Fin.cases row165Interface <| Fin.cases row166Interface <| Fin.cases row167Interface <| Fin.cases row168Interface <| Fin.cases row169Interface <| Fin.cases row170Interface <| Fin.cases row171Interface <| Fin.cases row172Interface <| Fin.cases row173Interface <| Fin.cases row174Interface <| Fin.cases row175Interface <| Fin.cases row176Interface <| Fin.cases row177Interface <| Fin.cases row178Interface <| Fin.cases row179Interface <| Fin.cases row180Interface <| Fin.cases row181Interface <| Fin.cases row182Interface <| Fin.cases row183Interface <| Fin.cases row184Interface <| Fin.cases row185Interface <| Fin.cases row186Interface <| Fin.cases row187Interface <| Fin.cases row188Interface <| Fin.cases row189Interface <| Fin.cases row190Interface <| Fin.cases row191Interface <| Fin.cases row192Interface <| Fin.cases row193Interface <| Fin.cases row194Interface <| Fin.cases row195Interface <| Fin.cases row196Interface <| Fin.cases row197Interface <| Fin.cases row198Interface <| Fin.cases row199Interface <| Fin.cases row200Interface <| Fin.cases row201Interface <| Fin.cases row202Interface <| Fin.cases row203Interface <| Fin.cases row204Interface <| Fin.cases row205Interface <| Fin.cases row206Interface <| Fin.cases row207Interface <| Fin.cases row208Interface <| Fin.cases row209Interface <| Fin.cases row210Interface <| Fin.cases row211Interface <| Fin.cases row212Interface <| Fin.cases row213Interface <| Fin.cases row214Interface <| Fin.cases row215Interface <| Fin.cases row216Interface <| Fin.cases row217Interface <| Fin.cases row218Interface <| Fin.cases row219Interface <| Fin.cases row220Interface <| Fin.cases row221Interface <| Fin.cases row222Interface <| Fin.cases row223Interface <| Fin.cases row224Interface <| Fin.cases row225Interface <| Fin.cases row226Interface <| Fin.cases row227Interface <| Fin.cases row228Interface <| Fin.cases row229Interface <| Fin.cases row230Interface <| Fin.cases row231Interface <| Fin.cases row232Interface <| Fin.cases row233Interface <| Fin.cases row234Interface <| Fin.cases row235Interface <| Fin.cases row236Interface <| Fin.cases row237Interface <| Fin.cases row238Interface <| Fin.cases row239Interface <| Fin.cases row240Interface <| Fin.cases row241Interface <| Fin.cases row242Interface <| Fin.cases row243Interface <| Fin.cases row244Interface <| Fin.cases row245Interface <| Fin.cases row246Interface <| Fin.cases row247Interface <| Fin.cases row248Interface <| Fin.cases row249Interface <| Fin.cases row250Interface <| Fin.cases row251Interface <| Fin.cases row252Interface <| Fin.cases row253Interface <| Fin.cases row254Interface <| Fin.cases row255Interface <| Fin.cases row256Interface <| Fin.cases row257Interface <| Fin.cases row258Interface <| Fin.cases row259Interface <| Fin.cases row260Interface <| Fin.cases row261Interface <| Fin.cases row262Interface <| Fin.cases row263Interface <| Fin.cases row264Interface <| Fin.cases row265Interface <| Fin.cases row266Interface <| Fin.cases row267Interface <| Fin.cases row268Interface <| Fin.cases row269Interface <| Fin.cases row270Interface <| Fin.cases row271Interface <| Fin.cases row272Interface <| Fin.cases row273Interface <| Fin.cases row274Interface <| Fin.cases row275Interface <| Fin.cases row276Interface <| Fin.cases row277Interface <| Fin.cases row278Interface <| Fin.cases row279Interface <| Fin.cases row280Interface <| Fin.cases row281Interface <| Fin.cases row282Interface <| Fin.cases row283Interface <| Fin.cases row284Interface <| Fin.cases row285Interface <| Fin.cases row286Interface <| Fin.cases row287Interface <| Fin.cases row288Interface <| Fin.cases row289Interface <| Fin.cases row290Interface <| Fin.cases row291Interface <| Fin.cases row292Interface <| Fin.cases row293Interface <| Fin.cases row294Interface <| Fin.cases row295Interface <| Fin.cases row296Interface <| Fin.cases row297Interface <| Fin.cases row298Interface <| Fin.cases row299Interface <| Fin.cases row300Interface <| Fin.cases row301Interface <| Fin.elim0

noncomputable def row (j : Fin 301) : DegreeTwoTwelvePairTopRow where
  finite := finiteInterface j
  branch := branch j
  kappa := kappa j
  sectionCap := sectionCap j
  expectedProfiles :=
    match branch j with
    | .joint => degreeTwoTwelvePairJointProfiles (kappa j) (sectionCap j)
    | .core => degreeTwoTwelvePairExceptionalProfiles
    | .ternary => ∅
    | .paired => degreeTwoTwelvePairExceptionalProfiles
  expectedProfiles_eq := rfl

noncomputable def pairedSix : Fin 2 → DegreeTwoPairTopFiniteInterface 6 :=
  Fin.cases pairedSix1Interface <| Fin.cases pairedSix2Interface Fin.elim0

private def pairedPosition : Fin 2 → Fin 301 := ![194, 235]

private def pairedForward
    (j : {j : Fin 301 // (row j).branch = .paired}) : Fin 2 :=
  if j.1.val = 194 then 0 else 1

private def pairedBackward
    (i : Fin 2) : {j : Fin 301 // (row j).branch = .paired} :=
  ⟨pairedPosition i, by fin_cases i <;> native_decide⟩

private def pairedBinding :
    {j : Fin 301 // (row j).branch = .paired} ≃ Fin 2 where
  toFun := pairedForward
  invFun := pairedBackward
  left_inv := by native_decide +revert
  right_inv := by native_decide +revert

noncomputable def catalogue : DegreeTwoTwelvePairTopFiniteCatalogue where
  row := row
  pairedSix := pairedSix
  pairedSixBinding := pairedBinding
  joint_count := by native_decide
  core_count := by native_decide
  ternary_count := by native_decide
  paired_count := by native_decide

end DegreeTwoTwelvePairFiniteCatalogue
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
