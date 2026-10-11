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

end DegreeTwoTwelvePairFiniteCatalogue
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
