import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopCatalogues

/-! Generated literal interfaces for the pinned pair-top action family.
The generator arrays are theorem data; registry completeness is
semantic and does not trust a JSON census flag. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPrimitiveSixteenInterfaces

private def row1Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 15, 1, 14, 2, 13, 3, 12, 4, 11, 5, 10, 6, 9, 7, 8] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 4, 6, 8, 10, 12, 14, 15, 13, 11, 9, 7, 5, 3, 1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row1Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row1Generators : Fin 2 → Equiv.Perm (Fin 16) :=
  ![row1Generator0, row1Generator1]

abbrev Row1Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row1Generators)

noncomputable def row1 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row1Top

private def row2Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 8, 15, 7, 2, 10, 13, 5, 4, 12, 11, 3, 6, 14, 9, 1] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 15, 4, 11, 8, 7, 12, 3, 1, 14, 5, 10, 9, 6, 13, 2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row2Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 4, 15, 11, 1, 5, 14, 10, 8, 12, 7, 3, 9, 13, 6, 2] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 4, 15, 11, 1, 5, 14, 10, 8, 12, 7, 3, 9, 13, 6, 2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row2Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row2Generators : Fin 3 → Equiv.Perm (Fin 16) :=
  ![row2Generator0, row2Generator1, row2Generator2]

abbrev Row2Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row2Generators)

noncomputable def row2 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row2Top

private def row3Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 9, 1, 8, 2, 11, 3, 10, 4, 13, 5, 12, 6, 15, 7, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 4, 6, 8, 10, 12, 14, 3, 1, 7, 5, 11, 9, 15, 13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row3Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row3Generators : Fin 2 → Equiv.Perm (Fin 16) :=
  ![row3Generator0, row3Generator1]

abbrev Row3Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row3Generators)

noncomputable def row3 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row3Top

private def row4Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 12, 15, 13, 14, 4, 7, 5, 6, 8, 11, 9, 10] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 8, 10, 11, 9, 12, 14, 15, 13, 4, 6, 7, 5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row4Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 5, 10, 15, 1, 4, 11, 14, 2, 7, 8, 13, 3, 6, 9, 12] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 4, 8, 12, 5, 1, 13, 9, 10, 14, 2, 6, 15, 11, 7, 3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row4Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 5, 10, 15, 4, 1, 14, 11, 8, 13, 2, 7, 12, 9, 6, 3] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 5, 10, 15, 4, 1, 14, 11, 8, 13, 2, 7, 12, 9, 6, 3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row4Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row4Generators : Fin 4 → Equiv.Perm (Fin 16) :=
  ![row4Generator0, row4Generator1, row4Generator2, row4Generator3]

abbrev Row4Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row4Generators)

noncomputable def row4 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row4Top

private def row5Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 15, 1, 14, 2, 13, 3, 12, 4, 11, 5, 10, 6, 9, 7, 8] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 4, 6, 8, 10, 12, 14, 15, 13, 11, 9, 7, 5, 3, 1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row5Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 4, 15, 11, 2, 6, 13, 9, 8, 12, 7, 3, 10, 14, 5, 1] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 15, 4, 11, 1, 14, 5, 10, 8, 7, 12, 3, 9, 6, 13, 2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row5Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row5Generators : Fin 3 → Equiv.Perm (Fin 16) :=
  ![row5Generator0, row5Generator1, row5Generator2]

abbrev Row5Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row5Generators)

noncomputable def row5 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row5Top

private def row6Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 15, 4, 11, 2, 13, 6, 9, 8, 7, 12, 3, 10, 5, 14, 1] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 15, 4, 11, 2, 13, 6, 9, 8, 7, 12, 3, 10, 5, 14, 1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row6Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 10, 6, 12, 1, 11, 7, 13, 4, 14, 2, 8, 5, 15, 3, 9] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 4, 10, 14, 8, 12, 2, 6, 11, 15, 1, 5, 3, 7, 9, 13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row6Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row6Generators : Fin 3 → Equiv.Perm (Fin 16) :=
  ![row6Generator0, row6Generator1, row6Generator2]

abbrev Row6Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row6Generators)

noncomputable def row6 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row6Top

private def row7Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 12, 15, 13, 14, 4, 7, 5, 6, 8, 11, 9, 10] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 8, 10, 11, 9, 12, 14, 15, 13, 4, 6, 7, 5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row7Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 5, 10, 15, 1, 4, 11, 14, 2, 7, 8, 13, 3, 6, 9, 12] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 4, 8, 12, 5, 1, 13, 9, 10, 14, 2, 6, 15, 11, 7, 3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row7Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 5, 10, 15, 4, 1, 14, 11, 8, 13, 2, 7, 12, 9, 6, 3] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 5, 10, 15, 4, 1, 14, 11, 8, 13, 2, 7, 12, 9, 6, 3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row7Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 2, 1, 12, 15, 14, 13, 8, 11, 10, 9, 4, 7, 6, 5] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 3, 2, 1, 12, 15, 14, 13, 8, 11, 10, 9, 4, 7, 6, 5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row7Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row7Generators : Fin 5 → Equiv.Perm (Fin 16) :=
  ![row7Generator0, row7Generator1, row7Generator2, row7Generator3, row7Generator4]

abbrev Row7Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row7Generators)

noncomputable def row7 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row7Top

private def row8Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 12, 15, 13, 14, 4, 7, 5, 6, 8, 11, 9, 10] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 8, 10, 11, 9, 12, 14, 15, 13, 4, 6, 7, 5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row8Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 5, 10, 15, 1, 4, 11, 14, 2, 7, 8, 13, 3, 6, 9, 12] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 4, 8, 12, 5, 1, 13, 9, 10, 14, 2, 6, 15, 11, 7, 3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row8Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 12, 15, 2, 1, 14, 13, 8, 11, 4, 7, 10, 9, 6, 5] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 5, 4, 1, 10, 15, 14, 11, 8, 13, 12, 9, 2, 7, 6, 3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row8Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row8Generators : Fin 4 → Equiv.Perm (Fin 16) :=
  ![row8Generator0, row8Generator1, row8Generator2, row8Generator3]

abbrev Row8Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row8Generators)

noncomputable def row8 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row8Top

private def row9Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 9, 1, 8, 2, 11, 3, 10, 4, 13, 5, 12, 6, 15, 7, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 4, 6, 8, 10, 12, 14, 3, 1, 7, 5, 11, 9, 15, 13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row9Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 15, 9, 6, 2, 13, 11, 4, 8, 7, 1, 14, 10, 5, 3, 12] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 10, 4, 14, 7, 13, 3, 9, 8, 2, 12, 6, 15, 5, 11, 1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row9Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row9Generators : Fin 3 → Equiv.Perm (Fin 16) :=
  ![row9Generator0, row9Generator1, row9Generator2]

abbrev Row9Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row9Generators)

noncomputable def row9 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row9Top

private def row10Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 12, 15, 13, 14, 4, 7, 5, 6, 8, 11, 9, 10] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 8, 10, 11, 9, 12, 14, 15, 13, 4, 6, 7, 5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row10Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 5, 10, 15, 1, 4, 11, 14, 2, 7, 8, 13, 3, 6, 9, 12] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 4, 8, 12, 5, 1, 13, 9, 10, 14, 2, 6, 15, 11, 7, 3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row10Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 5, 10, 15, 4, 1, 14, 11, 8, 13, 2, 7, 12, 9, 6, 3] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 5, 10, 15, 4, 1, 14, 11, 8, 13, 2, 7, 12, 9, 6, 3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row10Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 4, 5, 2, 3, 6, 7, 8, 9, 12, 13, 10, 11, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 4, 5, 2, 3, 6, 7, 8, 9, 12, 13, 10, 11, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row10Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row10Generators : Fin 5 → Equiv.Perm (Fin 16) :=
  ![row10Generator0, row10Generator1, row10Generator2, row10Generator3, row10Generator4]

abbrev Row10Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row10Generators)

noncomputable def row10 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row10Top

private def row11Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 13, 1, 12, 2, 15, 3, 14, 8, 5, 9, 4, 10, 7, 11, 6] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 4, 6, 11, 9, 15, 13, 8, 10, 12, 14, 3, 1, 7, 5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row11Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 7, 13, 10, 12, 11, 1, 6, 4, 3, 9, 14, 8, 15, 5, 2] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 6, 15, 9, 8, 14, 7, 1, 12, 10, 3, 5, 4, 2, 11, 13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row11Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row11Generators : Fin 3 → Equiv.Perm (Fin 16) :=
  ![row11Generator0, row11Generator1, row11Generator2]

abbrev Row11Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row11Generators)

noncomputable def row11 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row11Top

private def row12Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 9, 1, 8, 2, 11, 3, 10, 4, 13, 5, 12, 6, 15, 7, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 4, 6, 8, 10, 12, 14, 3, 1, 7, 5, 11, 9, 15, 13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row12Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 11, 10, 12, 13, 7, 6, 8, 9, 3, 2, 4, 5, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 11, 10, 12, 13, 7, 6, 8, 9, 3, 2, 4, 5, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row12Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row12Generators : Fin 3 → Equiv.Perm (Fin 16) :=
  ![row12Generator0, row12Generator1, row12Generator2]

abbrev Row12Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row12Generators)

noncomputable def row12 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row12Top

private def row13Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 9, 5, 12, 2, 11, 7, 14, 4, 13, 1, 8, 6, 15, 3, 10] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 10, 4, 14, 8, 2, 12, 6, 11, 1, 15, 5, 3, 9, 7, 13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row13Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 4, 10, 14, 1, 5, 11, 15, 8, 12, 2, 6, 9, 13, 3, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 4, 10, 14, 1, 5, 11, 15, 8, 12, 2, 6, 9, 13, 3, 7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row13Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row13Generators : Fin 3 → Equiv.Perm (Fin 16) :=
  ![row13Generator0, row13Generator1, row13Generator2]

abbrev Row13Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row13Generators)

noncomputable def row13 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row13Top

private def row14Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 6, 15, 9, 1, 7, 14, 8, 4, 2, 11, 13, 5, 3, 10, 12] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 4, 9, 13, 8, 12, 1, 5, 7, 3, 14, 10, 15, 11, 6, 2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row14Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 5, 10, 15, 1, 4, 11, 14, 2, 7, 8, 13, 3, 6, 9, 12] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 4, 8, 12, 5, 1, 13, 9, 10, 14, 2, 6, 15, 11, 7, 3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row14Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row14Generators : Fin 3 → Equiv.Perm (Fin 16) :=
  ![row14Generator0, row14Generator1, row14Generator2]

abbrev Row14Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row14Generators)

noncomputable def row14 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row14Top

private def row15Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 11, 9, 2, 1, 10, 8, 3, 4, 15, 13, 6, 5, 14, 12, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 4, 3, 7, 8, 12, 11, 15, 6, 2, 5, 1, 14, 10, 13, 9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row15Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 12, 10, 6, 15, 3, 5, 9, 2, 14, 8, 4, 13, 1, 7, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 13, 8, 5, 11, 6, 3, 14, 10, 7, 2, 15, 1, 12, 9, 4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row15Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row15Generators : Fin 3 → Equiv.Perm (Fin 16) :=
  ![row15Generator0, row15Generator1, row15Generator2]

abbrev Row15Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row15Generators)

noncomputable def row15 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row15Top

private def row16Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 12, 7, 11, 2, 14, 5, 9, 4, 8, 3, 15, 6, 10, 1, 13] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 14, 4, 10, 8, 6, 12, 2, 9, 7, 13, 3, 1, 15, 5, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row16Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 4, 15, 11, 1, 5, 14, 10, 8, 12, 7, 3, 9, 13, 6, 2] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 4, 15, 11, 1, 5, 14, 10, 8, 12, 7, 3, 9, 13, 6, 2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row16Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row16Generators : Fin 3 → Equiv.Perm (Fin 16) :=
  ![row16Generator0, row16Generator1, row16Generator2]

abbrev Row16Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row16Generators)

noncomputable def row16 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row16Top

private def row17Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 10, 3, 9, 1, 11, 2, 8, 4, 14, 7, 13, 5, 15, 6, 12] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 4, 6, 2, 8, 12, 14, 10, 7, 3, 1, 5, 15, 11, 9, 13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row17Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 13, 10, 7, 3, 14, 9, 4, 2, 15, 8, 5, 1, 12, 11, 6] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 12, 8, 4, 7, 11, 15, 3, 10, 6, 2, 14, 13, 1, 5, 9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row17Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row17Generators : Fin 3 → Equiv.Perm (Fin 16) :=
  ![row17Generator0, row17Generator1, row17Generator2]

abbrev Row17Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row17Generators)

noncomputable def row17 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row17Top

private def row18Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 15, 1, 14, 2, 13, 3, 12, 4, 11, 5, 10, 6, 9, 7, 8] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 4, 6, 8, 10, 12, 14, 15, 13, 11, 9, 7, 5, 3, 1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row18Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 15, 2, 13, 4, 11, 6, 9, 8, 7, 10, 5, 12, 3, 14, 1] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 15, 2, 13, 4, 11, 6, 9, 8, 7, 10, 5, 12, 3, 14, 1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row18Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row18Generators : Fin 3 → Equiv.Perm (Fin 16) :=
  ![row18Generator0, row18Generator1, row18Generator2]

abbrev Row18Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row18Generators)

noncomputable def row18 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row18Top

private def row19Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 15, 1, 14, 2, 13, 3, 12, 4, 11, 5, 10, 6, 9, 7, 8] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 4, 6, 8, 10, 12, 14, 15, 13, 11, 9, 7, 5, 3, 1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row19Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 4, 15, 11, 1, 5, 14, 10, 8, 12, 7, 3, 9, 13, 6, 2] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 4, 15, 11, 1, 5, 14, 10, 8, 12, 7, 3, 9, 13, 6, 2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row19Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row19Generators : Fin 3 → Equiv.Perm (Fin 16) :=
  ![row19Generator0, row19Generator1, row19Generator2]

abbrev Row19Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row19Generators)

noncomputable def row19 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row19Top

private def row20Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 12, 15, 13, 14, 4, 7, 5, 6, 8, 11, 9, 10] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 8, 10, 11, 9, 12, 14, 15, 13, 4, 6, 7, 5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row20Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 4, 11, 15, 2, 6, 9, 13, 8, 12, 3, 7, 10, 14, 1, 5] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 14, 4, 10, 1, 15, 5, 11, 8, 6, 12, 2, 9, 7, 13, 3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row20Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row20Generators : Fin 3 → Equiv.Perm (Fin 16) :=
  ![row20Generator0, row20Generator1, row20Generator2]

abbrev Row20Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row20Generators)

noncomputable def row20 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row20Top

noncomputable def interface : Fin 20 →
    DegreeTwoPairTopFiniteInterface 16 :=
  Fin.cases row1 <| Fin.cases row2 <| Fin.cases row3 <| Fin.cases row4 <| Fin.cases row5 <| Fin.cases row6 <| Fin.cases row7 <| Fin.cases row8 <| Fin.cases row9 <| Fin.cases row10 <| Fin.cases row11 <| Fin.cases row12 <| Fin.cases row13 <| Fin.cases row14 <| Fin.cases row15 <| Fin.cases row16 <| Fin.cases row17 <| Fin.cases row18 <| Fin.cases row19 <| Fin.cases row20 Fin.elim0

end DegreeTwoPrimitiveSixteenInterfaces
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
