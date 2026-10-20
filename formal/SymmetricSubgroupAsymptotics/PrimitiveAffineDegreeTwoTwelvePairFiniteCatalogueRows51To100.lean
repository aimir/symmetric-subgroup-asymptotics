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

end DegreeTwoTwelvePairFiniteCatalogue
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
