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

end DegreeTwoTwelvePairFiniteCatalogue
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
