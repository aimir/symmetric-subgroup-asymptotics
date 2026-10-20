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

end DegreeTwoTwelvePairFiniteCatalogue
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
