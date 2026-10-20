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
namespace DegreeTwoTwoAffineSixteenInterfaces

private def row1Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row1Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13] : Array (Fin 16))[x.val]!
  invFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row1Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row1Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 5, 7, 2, 3, 6, 4, 1, 8, 13, 15, 10, 11, 14, 12, 9] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 7, 3, 4, 6, 1, 5, 2, 8, 15, 11, 12, 14, 9, 13, 10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row1Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row1Generators : Fin 5 → Equiv.Perm (Fin 16) :=
  ![row1Generator0, row1Generator1, row1Generator2, row1Generator3, row1Generator4]

abbrev Row1Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row1Generators)

noncomputable def row1 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row1Top

private def row2Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6, 7, 4, 5, 2, 3, 0, 1, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[6, 7, 4, 5, 2, 3, 0, 1, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row2Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5, 4, 7, 6, 1, 0, 3, 2, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[5, 4, 7, 6, 1, 0, 3, 2, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row2Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row2Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 14, 15, 12, 13, 10, 11, 8, 9] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 14, 15, 12, 13, 10, 11, 8, 9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row2Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 13, 12, 15, 14, 9, 8, 11, 10] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 13, 12, 15, 14, 9, 8, 11, 10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row2Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row2Generator6 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row2Generator7 : Equiv.Perm (Fin 16) where
  toFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row2Generator8 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row2Generator9 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 5, 7, 2, 3, 6, 4, 1, 8, 13, 15, 10, 11, 14, 12, 9] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 7, 3, 4, 6, 1, 5, 2, 8, 15, 11, 12, 14, 9, 13, 10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row2Generator10 : Equiv.Perm (Fin 16) where
  toFun x := (#[8, 10, 12, 14, 13, 15, 9, 11, 4, 6, 0, 2, 1, 3, 5, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 12, 11, 13, 8, 14, 9, 15, 0, 6, 1, 7, 2, 4, 3, 5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row2Generators : Fin 11 → Equiv.Perm (Fin 16) :=
  ![row2Generator0, row2Generator1, row2Generator2, row2Generator3, row2Generator4, row2Generator5, row2Generator6, row2Generator7, row2Generator8, row2Generator9, row2Generator10]

abbrev Row2Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row2Generators)

noncomputable def row2 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row2Top

private def row3Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6, 7, 4, 5, 2, 3, 0, 1, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[6, 7, 4, 5, 2, 3, 0, 1, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row3Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5, 4, 7, 6, 1, 0, 3, 2, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[5, 4, 7, 6, 1, 0, 3, 2, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row3Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row3Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 14, 15, 12, 13, 10, 11, 8, 9] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 14, 15, 12, 13, 10, 11, 8, 9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row3Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 13, 12, 15, 14, 9, 8, 11, 10] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 13, 12, 15, 14, 9, 8, 11, 10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row3Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row3Generator6 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row3Generator7 : Equiv.Perm (Fin 16) where
  toFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row3Generator8 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row3Generator9 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 5, 7, 2, 3, 6, 4, 1, 8, 15, 11, 12, 14, 9, 13, 10] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 7, 3, 4, 6, 1, 5, 2, 8, 13, 15, 10, 11, 14, 12, 9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row3Generator10 : Equiv.Perm (Fin 16) where
  toFun x := (#[8, 14, 9, 15, 10, 12, 11, 13, 4, 6, 0, 2, 1, 3, 5, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 12, 11, 13, 8, 14, 9, 15, 0, 2, 4, 6, 5, 7, 1, 3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row3Generators : Fin 11 → Equiv.Perm (Fin 16) :=
  ![row3Generator0, row3Generator1, row3Generator2, row3Generator3, row3Generator4, row3Generator5, row3Generator6, row3Generator7, row3Generator8, row3Generator9, row3Generator10]

abbrev Row3Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row3Generators)

noncomputable def row3 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row3Top

private def row4Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row4Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row4Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row4Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 5, 7, 2, 3, 6, 4, 1, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 7, 3, 4, 6, 1, 5, 2, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row4Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row4Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 8, 9, 14, 15, 12, 13] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 8, 9, 14, 15, 12, 13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row4Generator6 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row4Generator7 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 13, 15, 10, 11, 14, 12, 9] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 15, 11, 12, 14, 9, 13, 10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row4Generator8 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row4Generator9 : Equiv.Perm (Fin 16) where
  toFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row4Generator10 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row4Generator11 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 5, 7, 2, 3, 6, 4, 1, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 7, 3, 4, 6, 1, 5, 2, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row4Generator12 : Equiv.Perm (Fin 16) where
  toFun x := (#[8, 9, 10, 11, 12, 13, 14, 15, 7, 6, 5, 4, 3, 2, 1, 0] : Array (Fin 16))[x.val]!
  invFun x := (#[15, 14, 13, 12, 11, 10, 9, 8, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row4Generators : Fin 13 → Equiv.Perm (Fin 16) :=
  ![row4Generator0, row4Generator1, row4Generator2, row4Generator3, row4Generator4, row4Generator5, row4Generator6, row4Generator7, row4Generator8, row4Generator9, row4Generator10, row4Generator11, row4Generator12]

abbrev Row4Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row4Generators)

noncomputable def row4 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row4Top

private def row5Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row5Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13] : Array (Fin 16))[x.val]!
  invFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row5Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row5Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 5, 7, 2, 3, 6, 4, 1, 8, 13, 15, 10, 11, 14, 12, 9] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 7, 3, 4, 6, 1, 5, 2, 8, 15, 11, 12, 14, 9, 13, 10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row5Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 4, 5, 7, 6, 3, 2, 8, 9, 12, 13, 15, 14, 11, 10] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 7, 6, 2, 3, 5, 4, 8, 9, 15, 14, 10, 11, 13, 12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row5Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row5Generators : Fin 6 → Equiv.Perm (Fin 16) :=
  ![row5Generator0, row5Generator1, row5Generator2, row5Generator3, row5Generator4, row5Generator5]

abbrev Row5Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row5Generators)

noncomputable def row5 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row5Top

private def row6Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6, 7, 4, 5, 2, 3, 0, 1, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[6, 7, 4, 5, 2, 3, 0, 1, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row6Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5, 4, 7, 6, 1, 0, 3, 2, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[5, 4, 7, 6, 1, 0, 3, 2, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row6Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row6Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 14, 15, 12, 13, 10, 11, 8, 9] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 14, 15, 12, 13, 10, 11, 8, 9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row6Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 13, 12, 15, 14, 9, 8, 11, 10] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 13, 12, 15, 14, 9, 8, 11, 10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row6Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row6Generator6 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row6Generator7 : Equiv.Perm (Fin 16) where
  toFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row6Generator8 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row6Generator9 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 5, 7, 2, 3, 6, 4, 1, 8, 13, 15, 10, 11, 14, 12, 9] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 7, 3, 4, 6, 1, 5, 2, 8, 15, 11, 12, 14, 9, 13, 10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row6Generator10 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 4, 5, 7, 6, 3, 2, 8, 9, 12, 13, 15, 14, 11, 10] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 7, 6, 2, 3, 5, 4, 8, 9, 15, 14, 10, 11, 13, 12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row6Generator11 : Equiv.Perm (Fin 16) where
  toFun x := (#[8, 12, 15, 11, 14, 10, 9, 13, 7, 3, 0, 4, 1, 5, 6, 2] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 12, 15, 9, 11, 13, 14, 8, 0, 6, 5, 3, 1, 7, 4, 2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row6Generators : Fin 12 → Equiv.Perm (Fin 16) :=
  ![row6Generator0, row6Generator1, row6Generator2, row6Generator3, row6Generator4, row6Generator5, row6Generator6, row6Generator7, row6Generator8, row6Generator9, row6Generator10, row6Generator11]

abbrev Row6Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row6Generators)

noncomputable def row6 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row6Top

private def row7Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6, 7, 4, 5, 2, 3, 0, 1, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[6, 7, 4, 5, 2, 3, 0, 1, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row7Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5, 4, 7, 6, 1, 0, 3, 2, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[5, 4, 7, 6, 1, 0, 3, 2, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row7Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row7Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 14, 15, 12, 13, 10, 11, 8, 9] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 14, 15, 12, 13, 10, 11, 8, 9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row7Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 13, 12, 15, 14, 9, 8, 11, 10] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 13, 12, 15, 14, 9, 8, 11, 10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row7Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row7Generator6 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row7Generator7 : Equiv.Perm (Fin 16) where
  toFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row7Generator8 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row7Generator9 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 5, 7, 2, 3, 6, 4, 1, 8, 15, 11, 12, 14, 9, 13, 10] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 7, 3, 4, 6, 1, 5, 2, 8, 13, 15, 10, 11, 14, 12, 9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row7Generator10 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 4, 5, 7, 6, 3, 2, 8, 13, 11, 14, 9, 12, 10, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 7, 6, 2, 3, 5, 4, 8, 12, 14, 10, 13, 9, 11, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row7Generator11 : Equiv.Perm (Fin 16) where
  toFun x := (#[8, 12, 15, 11, 14, 10, 9, 13, 3, 1, 6, 4, 0, 2, 5, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[12, 9, 13, 8, 11, 14, 10, 15, 0, 6, 5, 3, 1, 7, 4, 2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row7Generators : Fin 12 → Equiv.Perm (Fin 16) :=
  ![row7Generator0, row7Generator1, row7Generator2, row7Generator3, row7Generator4, row7Generator5, row7Generator6, row7Generator7, row7Generator8, row7Generator9, row7Generator10, row7Generator11]

abbrev Row7Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row7Generators)

noncomputable def row7 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row7Top

private def row8Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 5, 7, 2, 3, 6, 4, 1, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 7, 3, 4, 6, 1, 5, 2, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row8Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6, 7, 4, 5, 2, 3, 0, 1, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[6, 7, 4, 5, 2, 3, 0, 1, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row8Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5, 4, 7, 6, 1, 0, 3, 2, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[5, 4, 7, 6, 1, 0, 3, 2, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row8Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row8Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 13, 15, 10, 11, 14, 12, 9] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 15, 11, 12, 14, 9, 13, 10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row8Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 14, 15, 12, 13, 10, 11, 8, 9] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 14, 15, 12, 13, 10, 11, 8, 9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row8Generator6 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 13, 12, 15, 14, 9, 8, 11, 10] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 13, 12, 15, 14, 9, 8, 11, 10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row8Generator7 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row8Generator8 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row8Generator9 : Equiv.Perm (Fin 16) where
  toFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row8Generator10 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row8Generator11 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 5, 7, 2, 3, 6, 4, 1, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 7, 3, 4, 6, 1, 5, 2, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row8Generator12 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 4, 5, 7, 6, 3, 2, 8, 9, 12, 13, 15, 14, 11, 10] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 7, 6, 2, 3, 5, 4, 8, 9, 15, 14, 10, 11, 13, 12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row8Generator13 : Equiv.Perm (Fin 16) where
  toFun x := (#[8, 12, 15, 11, 14, 10, 9, 13, 5, 7, 0, 2, 6, 4, 3, 1] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 15, 11, 14, 13, 8, 12, 9, 0, 6, 5, 3, 1, 7, 4, 2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row8Generators : Fin 14 → Equiv.Perm (Fin 16) :=
  ![row8Generator0, row8Generator1, row8Generator2, row8Generator3, row8Generator4, row8Generator5, row8Generator6, row8Generator7, row8Generator8, row8Generator9, row8Generator10, row8Generator11, row8Generator12, row8Generator13]

abbrev Row8Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row8Generators)

noncomputable def row8 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row8Top

private def row9Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 5, 7, 2, 3, 6, 4, 1, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 7, 3, 4, 6, 1, 5, 2, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row9Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6, 7, 4, 5, 2, 3, 0, 1, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[6, 7, 4, 5, 2, 3, 0, 1, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row9Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5, 4, 7, 6, 1, 0, 3, 2, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[5, 4, 7, 6, 1, 0, 3, 2, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row9Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row9Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 13, 15, 10, 11, 14, 12, 9] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 15, 11, 12, 14, 9, 13, 10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row9Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 14, 15, 12, 13, 10, 11, 8, 9] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 14, 15, 12, 13, 10, 11, 8, 9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row9Generator6 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 13, 12, 15, 14, 9, 8, 11, 10] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 13, 12, 15, 14, 9, 8, 11, 10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row9Generator7 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row9Generator8 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row9Generator9 : Equiv.Perm (Fin 16) where
  toFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row9Generator10 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row9Generator11 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 5, 7, 2, 3, 6, 4, 1, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 7, 3, 4, 6, 1, 5, 2, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row9Generator12 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 4, 5, 7, 6, 3, 2, 8, 9, 15, 14, 10, 11, 13, 12] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 7, 6, 2, 3, 5, 4, 8, 9, 12, 13, 15, 14, 11, 10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row9Generator13 : Equiv.Perm (Fin 16) where
  toFun x := (#[8, 15, 10, 13, 11, 12, 9, 14, 5, 7, 0, 2, 6, 4, 3, 1] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 15, 11, 14, 13, 8, 12, 9, 0, 6, 2, 4, 5, 3, 7, 1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row9Generators : Fin 14 → Equiv.Perm (Fin 16) :=
  ![row9Generator0, row9Generator1, row9Generator2, row9Generator3, row9Generator4, row9Generator5, row9Generator6, row9Generator7, row9Generator8, row9Generator9, row9Generator10, row9Generator11, row9Generator12, row9Generator13]

abbrev Row9Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row9Generators)

noncomputable def row9 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row9Top

private def row10Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row10Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row10Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row10Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 5, 7, 2, 3, 6, 4, 1, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 7, 3, 4, 6, 1, 5, 2, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row10Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 4, 5, 7, 6, 3, 2, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 7, 6, 2, 3, 5, 4, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row10Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row10Generator6 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 8, 9, 14, 15, 12, 13] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 8, 9, 14, 15, 12, 13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row10Generator7 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row10Generator8 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 13, 15, 10, 11, 14, 12, 9] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 15, 11, 12, 14, 9, 13, 10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row10Generator9 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 15, 14, 11, 10] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 14, 10, 11, 13, 12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row10Generator10 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row10Generator11 : Equiv.Perm (Fin 16) where
  toFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row10Generator12 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row10Generator13 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 5, 7, 2, 3, 6, 4, 1, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 7, 3, 4, 6, 1, 5, 2, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row10Generator14 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 4, 5, 7, 6, 3, 2, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 7, 6, 2, 3, 5, 4, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row10Generator15 : Equiv.Perm (Fin 16) where
  toFun x := (#[8, 9, 10, 11, 12, 13, 14, 15, 7, 6, 5, 4, 3, 2, 1, 0] : Array (Fin 16))[x.val]!
  invFun x := (#[15, 14, 13, 12, 11, 10, 9, 8, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row10Generators : Fin 16 → Equiv.Perm (Fin 16) :=
  ![row10Generator0, row10Generator1, row10Generator2, row10Generator3, row10Generator4, row10Generator5, row10Generator6, row10Generator7, row10Generator8, row10Generator9, row10Generator10, row10Generator11, row10Generator12, row10Generator13, row10Generator14, row10Generator15]

abbrev Row10Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row10Generators)

noncomputable def row10 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row10Top

private def row11Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row11Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13] : Array (Fin 16))[x.val]!
  invFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row11Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row11Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 6, 7, 4, 5, 8, 9, 10, 11, 14, 15, 12, 13] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 6, 7, 4, 5, 8, 9, 10, 11, 14, 15, 12, 13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row11Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 2, 4, 6, 1, 3, 5, 7, 8, 10, 12, 14, 9, 11, 13, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 4, 1, 5, 2, 6, 3, 7, 8, 12, 9, 13, 10, 14, 11, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row11Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row11Generators : Fin 6 → Equiv.Perm (Fin 16) :=
  ![row11Generator0, row11Generator1, row11Generator2, row11Generator3, row11Generator4, row11Generator5]

abbrev Row11Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row11Generators)

noncomputable def row11 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row11Top

private def row12Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row12Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13] : Array (Fin 16))[x.val]!
  invFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row12Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row12Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 6, 7, 4, 5, 11, 10, 9, 8, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 6, 7, 4, 5, 11, 10, 9, 8, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row12Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 2, 4, 6, 1, 3, 5, 7, 14, 12, 10, 8, 15, 13, 11, 9] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 4, 1, 5, 2, 6, 3, 7, 11, 15, 10, 14, 9, 13, 8, 12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row12Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row12Generators : Fin 6 → Equiv.Perm (Fin 16) :=
  ![row12Generator0, row12Generator1, row12Generator2, row12Generator3, row12Generator4, row12Generator5]

abbrev Row12Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row12Generators)

noncomputable def row12 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row12Top

private def row13Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row13Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row13Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row13Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row13Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row13Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 8, 9, 14, 15, 12, 13] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 8, 9, 14, 15, 12, 13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row13Generator6 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row13Generator7 : Equiv.Perm (Fin 16) where
  toFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row13Generator8 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row13Generator9 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 6, 7, 4, 5, 8, 9, 10, 11, 14, 15, 12, 13] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 6, 7, 4, 5, 8, 9, 10, 11, 14, 15, 12, 13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row13Generator10 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 2, 4, 6, 1, 3, 5, 7, 8, 10, 12, 14, 9, 11, 13, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 4, 1, 5, 2, 6, 3, 7, 8, 12, 9, 13, 10, 14, 11, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row13Generator11 : Equiv.Perm (Fin 16) where
  toFun x := (#[8, 9, 12, 13, 10, 11, 14, 15, 7, 6, 3, 2, 5, 4, 1, 0] : Array (Fin 16))[x.val]!
  invFun x := (#[15, 14, 11, 10, 13, 12, 9, 8, 0, 1, 4, 5, 2, 3, 6, 7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row13Generators : Fin 12 → Equiv.Perm (Fin 16) :=
  ![row13Generator0, row13Generator1, row13Generator2, row13Generator3, row13Generator4, row13Generator5, row13Generator6, row13Generator7, row13Generator8, row13Generator9, row13Generator10, row13Generator11]

abbrev Row13Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row13Generators)

noncomputable def row13 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row13Top

private def row14Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row14Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row14Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row14Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row14Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row14Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 8, 9, 14, 15, 12, 13] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 8, 9, 14, 15, 12, 13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row14Generator6 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row14Generator7 : Equiv.Perm (Fin 16) where
  toFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row14Generator8 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row14Generator9 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 6, 7, 4, 5, 8, 9, 11, 10, 12, 13, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 6, 7, 4, 5, 8, 9, 11, 10, 12, 13, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row14Generator10 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 2, 4, 6, 1, 3, 5, 7, 8, 12, 9, 13, 10, 14, 11, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 4, 1, 5, 2, 6, 3, 7, 8, 10, 12, 14, 9, 11, 13, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row14Generator11 : Equiv.Perm (Fin 16) where
  toFun x := (#[8, 9, 12, 13, 10, 11, 14, 15, 7, 5, 6, 4, 3, 1, 2, 0] : Array (Fin 16))[x.val]!
  invFun x := (#[15, 13, 14, 12, 11, 9, 10, 8, 0, 1, 4, 5, 2, 3, 6, 7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row14Generators : Fin 12 → Equiv.Perm (Fin 16) :=
  ![row14Generator0, row14Generator1, row14Generator2, row14Generator3, row14Generator4, row14Generator5, row14Generator6, row14Generator7, row14Generator8, row14Generator9, row14Generator10, row14Generator11]

abbrev Row14Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row14Generators)

noncomputable def row14 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row14Top

private def row15Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row15Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row15Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row15Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row15Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 2, 4, 6, 1, 3, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 4, 1, 5, 2, 6, 3, 7, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row15Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row15Generator6 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 8, 9, 14, 15, 12, 13] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 8, 9, 14, 15, 12, 13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row15Generator7 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row15Generator8 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 12, 13] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 12, 13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row15Generator9 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 9, 11, 13, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 9, 13, 10, 14, 11, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row15Generator10 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row15Generator11 : Equiv.Perm (Fin 16) where
  toFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row15Generator12 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row15Generator13 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row15Generator14 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 2, 4, 6, 1, 3, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 4, 1, 5, 2, 6, 3, 7, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row15Generator15 : Equiv.Perm (Fin 16) where
  toFun x := (#[8, 9, 10, 11, 12, 13, 14, 15, 7, 6, 5, 4, 3, 2, 1, 0] : Array (Fin 16))[x.val]!
  invFun x := (#[15, 14, 13, 12, 11, 10, 9, 8, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row15Generators : Fin 16 → Equiv.Perm (Fin 16) :=
  ![row15Generator0, row15Generator1, row15Generator2, row15Generator3, row15Generator4, row15Generator5, row15Generator6, row15Generator7, row15Generator8, row15Generator9, row15Generator10, row15Generator11, row15Generator12, row15Generator13, row15Generator14, row15Generator15]

abbrev Row15Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row15Generators)

noncomputable def row15 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row15Top

noncomputable def interface : Fin 15 →
    DegreeTwoPairTopFiniteInterface 16 :=
  Fin.cases row1 <| Fin.cases row2 <| Fin.cases row3 <| Fin.cases row4 <| Fin.cases row5 <| Fin.cases row6 <| Fin.cases row7 <| Fin.cases row8 <| Fin.cases row9 <| Fin.cases row10 <| Fin.cases row11 <| Fin.cases row12 <| Fin.cases row13 <| Fin.cases row14 <| Fin.cases row15 Fin.elim0

end DegreeTwoTwoAffineSixteenInterfaces
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
