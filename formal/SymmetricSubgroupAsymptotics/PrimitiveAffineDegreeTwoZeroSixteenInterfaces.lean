import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopCatalogues
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow1NormalCertificate

/-! Generated literal interfaces for the pinned pair-top action family.
The generator arrays are theorem data; registry completeness is
semantic and does not trust a JSON census flag. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoZeroSixteenInterfaces

noncomputable def row1 : DegreeTwoPairTopFiniteInterface 16 := by
  letI : Group PrimitiveAffineSixteenFrameRow1TopCertificate.Source :=
    PrimitiveAffineSixteenFrameRow1TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineSixteenFrameRow1NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineSixteenFrameRow1NormalCertificate.topAmbient
    PrimitiveAffineSixteenFrameRow1NormalCertificate.stateGenerators
    PrimitiveAffineSixteenFrameRow1NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineSixteenFrameRow1TopCertificate.generators))
    PrimitiveAffineSixteenFrameRow1TopCertificate.originalEquiv

private def row2Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 8, 10, 11, 9, 15, 14, 13, 12, 6, 5, 7, 4] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 15, 13, 12, 14, 4, 7, 5, 6, 11, 10, 9, 8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row2Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11, 9, 8, 10, 15, 14, 13, 12, 1, 2, 0, 3, 5, 4, 7, 6] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 8, 9, 11, 13, 12, 15, 14, 2, 1, 3, 0, 7, 6, 5, 4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row2Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6, 5, 7, 4, 2, 0, 1, 3, 12, 14, 15, 13, 10, 9, 11, 8] : Array (Fin 16))[x.val]!
  invFun x := (#[5, 6, 4, 7, 3, 1, 0, 2, 15, 13, 12, 14, 8, 11, 9, 10] : Array (Fin 16))[x.val]!
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
  toFun x := (#[0, 3, 1, 2, 11, 9, 8, 10, 12, 13, 14, 15, 4, 7, 5, 6] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 12, 14, 15, 13, 6, 5, 7, 4, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row3Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10, 8, 9, 11, 12, 13, 14, 15, 1, 2, 0, 3, 4, 5, 6, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 8, 9, 11, 12, 13, 14, 15, 1, 2, 0, 3, 4, 5, 6, 7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row3Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5, 6, 4, 7, 2, 0, 1, 3, 14, 12, 13, 15, 9, 10, 8, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[5, 6, 4, 7, 2, 0, 1, 3, 14, 12, 13, 15, 9, 10, 8, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row3Generators : Fin 3 → Equiv.Perm (Fin 16) :=
  ![row3Generator0, row3Generator1, row3Generator2]

abbrev Row3Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row3Generators)

noncomputable def row3 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row3Top

private def row4Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 11, 9, 8, 10, 12, 13, 14, 15, 4, 7, 5, 6] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 12, 14, 15, 13, 6, 5, 7, 4, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row4Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11, 9, 8, 10, 14, 15, 12, 13, 1, 2, 0, 3, 4, 5, 6, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 8, 9, 11, 12, 13, 14, 15, 2, 1, 3, 0, 6, 7, 4, 5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row4Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 7, 5, 6, 2, 0, 1, 3, 13, 15, 14, 12, 8, 11, 9, 10] : Array (Fin 16))[x.val]!
  invFun x := (#[5, 6, 4, 7, 0, 2, 3, 1, 12, 14, 15, 13, 11, 8, 10, 9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row4Generators : Fin 3 → Equiv.Perm (Fin 16) :=
  ![row4Generator0, row4Generator1, row4Generator2]

abbrev Row4Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row4Generators)

noncomputable def row4 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row4Top

private def row5Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 11, 9, 8, 10, 12, 13, 14, 15, 4, 7, 5, 6] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 12, 14, 15, 13, 6, 5, 7, 4, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row5Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10, 8, 9, 11, 13, 12, 15, 14, 1, 2, 0, 3, 5, 4, 7, 6] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 8, 9, 11, 13, 12, 15, 14, 1, 2, 0, 3, 5, 4, 7, 6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row5Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5, 6, 4, 7, 2, 0, 1, 3, 12, 14, 15, 13, 8, 11, 9, 10] : Array (Fin 16))[x.val]!
  invFun x := (#[5, 6, 4, 7, 2, 0, 1, 3, 12, 14, 15, 13, 8, 11, 9, 10] : Array (Fin 16))[x.val]!
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
  toFun x := (#[0, 3, 1, 2, 11, 9, 8, 10, 13, 12, 15, 14, 5, 6, 4, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 14, 12, 13, 15, 6, 5, 7, 4, 9, 8, 11, 10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row6Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10, 8, 9, 11, 12, 13, 14, 15, 1, 2, 0, 3, 4, 5, 6, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 8, 9, 11, 12, 13, 14, 15, 1, 2, 0, 3, 4, 5, 6, 7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row6Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5, 6, 4, 7, 2, 0, 1, 3, 14, 12, 13, 15, 9, 10, 8, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[5, 6, 4, 7, 2, 0, 1, 3, 14, 12, 13, 15, 9, 10, 8, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row6Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[2, 3, 0, 1, 7, 6, 5, 4, 9, 8, 11, 10, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[2, 3, 0, 1, 7, 6, 5, 4, 9, 8, 11, 10, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row6Generators : Fin 4 → Equiv.Perm (Fin 16) :=
  ![row6Generator0, row6Generator1, row6Generator2, row6Generator3]

abbrev Row6Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row6Generators)

noncomputable def row6 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row6Top

private def row7Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 11, 9, 8, 10, 12, 13, 14, 15, 4, 7, 5, 6] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 12, 14, 15, 13, 6, 5, 7, 4, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row7Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10, 8, 9, 11, 12, 13, 14, 15, 1, 2, 0, 3, 4, 5, 6, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 8, 9, 11, 12, 13, 14, 15, 1, 2, 0, 3, 4, 5, 6, 7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row7Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5, 6, 4, 7, 2, 0, 1, 3, 14, 12, 13, 15, 9, 10, 8, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[5, 6, 4, 7, 2, 0, 1, 3, 14, 12, 13, 15, 9, 10, 8, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row7Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 5, 4, 7, 6, 10, 11, 8, 9, 14, 15, 12, 13] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 5, 4, 7, 6, 10, 11, 8, 9, 14, 15, 12, 13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row7Generators : Fin 4 → Equiv.Perm (Fin 16) :=
  ![row7Generator0, row7Generator1, row7Generator2, row7Generator3]

abbrev Row7Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row7Generators)

noncomputable def row7 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row7Top

private def row8Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 11, 9, 8, 10, 12, 13, 14, 15, 4, 7, 5, 6] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 12, 14, 15, 13, 6, 5, 7, 4, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row8Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9, 11, 10, 8, 13, 12, 15, 14, 1, 2, 0, 3, 4, 5, 6, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 8, 9, 11, 12, 13, 14, 15, 3, 0, 2, 1, 5, 4, 7, 6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row8Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5, 6, 4, 7, 2, 0, 1, 3, 13, 15, 14, 12, 11, 8, 10, 9] : Array (Fin 16))[x.val]!
  invFun x := (#[5, 6, 4, 7, 2, 0, 1, 3, 13, 15, 14, 12, 11, 8, 10, 9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row8Generators : Fin 3 → Equiv.Perm (Fin 16) :=
  ![row8Generator0, row8Generator1, row8Generator2]

abbrev Row8Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row8Generators)

noncomputable def row8 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row8Top

private def row9Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 8, 10, 11, 9, 12, 13, 14, 15, 5, 6, 4, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 14, 12, 13, 15, 4, 7, 5, 6, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row9Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10, 8, 9, 11, 12, 13, 14, 15, 1, 2, 0, 3, 4, 5, 6, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 8, 9, 11, 12, 13, 14, 15, 1, 2, 0, 3, 4, 5, 6, 7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row9Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5, 6, 4, 7, 2, 0, 1, 3, 14, 12, 13, 15, 9, 10, 8, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[5, 6, 4, 7, 2, 0, 1, 3, 14, 12, 13, 15, 9, 10, 8, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row9Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[2, 3, 0, 1, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[2, 3, 0, 1, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row9Generators : Fin 4 → Equiv.Perm (Fin 16) :=
  ![row9Generator0, row9Generator1, row9Generator2, row9Generator3]

abbrev Row9Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row9Generators)

noncomputable def row9 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row9Top

private def row10Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 8, 10, 11, 9, 12, 13, 14, 15, 5, 6, 4, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 14, 12, 13, 15, 4, 7, 5, 6, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row10Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10, 8, 9, 11, 15, 14, 13, 12, 1, 2, 0, 3, 4, 5, 6, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 8, 9, 11, 12, 13, 14, 15, 1, 2, 0, 3, 7, 6, 5, 4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row10Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5, 6, 4, 7, 2, 0, 1, 3, 15, 13, 12, 14, 9, 10, 8, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[5, 6, 4, 7, 2, 0, 1, 3, 14, 12, 13, 15, 10, 9, 11, 8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row10Generators : Fin 3 → Equiv.Perm (Fin 16) :=
  ![row10Generator0, row10Generator1, row10Generator2]

abbrev Row10Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row10Generators)

noncomputable def row10 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row10Top

private def row11Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 8, 10, 11, 9, 12, 13, 14, 15, 5, 6, 4, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 14, 12, 13, 15, 4, 7, 5, 6, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row11Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10, 8, 9, 11, 12, 13, 14, 15, 1, 2, 0, 3, 4, 5, 6, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 8, 9, 11, 12, 13, 14, 15, 1, 2, 0, 3, 4, 5, 6, 7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row11Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5, 6, 4, 7, 2, 0, 1, 3, 14, 12, 13, 15, 9, 10, 8, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[5, 6, 4, 7, 2, 0, 1, 3, 14, 12, 13, 15, 9, 10, 8, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row11Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[2, 3, 0, 1, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[2, 3, 0, 1, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row11Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 14, 15, 12, 13] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 14, 15, 12, 13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row11Generators : Fin 5 → Equiv.Perm (Fin 16) :=
  ![row11Generator0, row11Generator1, row11Generator2, row11Generator3, row11Generator4]

abbrev Row11Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row11Generators)

noncomputable def row11 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row11Top

private def row12Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 8, 10, 11, 9, 12, 13, 14, 15, 5, 6, 4, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 14, 12, 13, 15, 4, 7, 5, 6, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row12Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10, 8, 9, 11, 14, 15, 12, 13, 1, 2, 0, 3, 4, 5, 6, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 8, 9, 11, 12, 13, 14, 15, 1, 2, 0, 3, 6, 7, 4, 5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row12Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5, 6, 4, 7, 2, 0, 1, 3, 13, 15, 14, 12, 9, 10, 8, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[5, 6, 4, 7, 2, 0, 1, 3, 14, 12, 13, 15, 11, 8, 10, 9] : Array (Fin 16))[x.val]!
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
  toFun x := (#[0, 3, 1, 2, 10, 8, 9, 11, 12, 13, 14, 15, 5, 6, 4, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 14, 12, 13, 15, 5, 6, 4, 7, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row13Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10, 8, 9, 11, 12, 13, 14, 15, 1, 2, 0, 3, 4, 5, 6, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 8, 9, 11, 12, 13, 14, 15, 1, 2, 0, 3, 4, 5, 6, 7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row13Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5, 6, 4, 7, 2, 0, 1, 3, 14, 12, 13, 15, 9, 10, 8, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[5, 6, 4, 7, 2, 0, 1, 3, 14, 12, 13, 15, 9, 10, 8, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row13Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row13Generators : Fin 4 → Equiv.Perm (Fin 16) :=
  ![row13Generator0, row13Generator1, row13Generator2, row13Generator3]

abbrev Row13Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row13Generators)

noncomputable def row13 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row13Top

private def row14Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 3, 2, 9, 8, 11, 10, 5, 4, 7, 6, 12, 14, 13, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 3, 2, 9, 8, 11, 10, 5, 4, 7, 6, 12, 14, 13, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row14Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 10, 8, 11, 9, 15, 14, 13, 12, 6, 4, 7, 5] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 13, 15, 12, 14, 5, 7, 4, 6, 11, 10, 9, 8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row14Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 6, 5, 7, 0, 2, 1, 3, 14, 12, 13, 15, 9, 10, 8, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 6, 5, 7, 0, 2, 1, 3, 14, 12, 13, 15, 9, 10, 8, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row14Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[10, 8, 9, 11, 13, 12, 14, 15, 1, 2, 0, 3, 5, 4, 6, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 8, 9, 11, 13, 12, 14, 15, 1, 2, 0, 3, 5, 4, 6, 7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row14Generators : Fin 4 → Equiv.Perm (Fin 16) :=
  ![row14Generator0, row14Generator1, row14Generator2, row14Generator3]

abbrev Row14Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row14Generators)

noncomputable def row14 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row14Top

private def row15Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 3, 2, 9, 8, 11, 10, 5, 4, 7, 6, 12, 14, 13, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 3, 2, 9, 8, 11, 10, 5, 4, 7, 6, 12, 14, 13, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row15Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 10, 8, 11, 9, 15, 14, 13, 12, 6, 4, 7, 5] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 13, 15, 12, 14, 5, 7, 4, 6, 11, 10, 9, 8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row15Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7, 5, 6, 4, 0, 2, 1, 3, 15, 13, 12, 14, 11, 8, 10, 9] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 6, 5, 7, 3, 1, 2, 0, 13, 15, 14, 12, 10, 9, 11, 8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row15Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9, 11, 10, 8, 15, 14, 12, 13, 1, 2, 0, 3, 7, 6, 4, 5] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 8, 9, 11, 14, 15, 13, 12, 3, 0, 2, 1, 6, 7, 5, 4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row15Generators : Fin 4 → Equiv.Perm (Fin 16) :=
  ![row15Generator0, row15Generator1, row15Generator2, row15Generator3]

abbrev Row15Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row15Generators)

noncomputable def row15 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row15Top

private def row16Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 2, 1, 3, 4, 6, 5, 7, 12, 14, 13, 15, 8, 10, 9, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 1, 3, 4, 6, 5, 7, 12, 14, 13, 15, 8, 10, 9, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row16Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 9, 11, 8, 10, 12, 13, 14, 15, 5, 7, 4, 6] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 14, 12, 15, 13, 6, 4, 7, 5, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row16Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 6, 5, 7, 0, 2, 1, 3, 14, 12, 13, 15, 9, 10, 8, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 6, 5, 7, 0, 2, 1, 3, 14, 12, 13, 15, 9, 10, 8, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row16Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[10, 8, 9, 11, 13, 12, 14, 15, 1, 2, 0, 3, 5, 4, 6, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 8, 9, 11, 13, 12, 14, 15, 1, 2, 0, 3, 5, 4, 6, 7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row16Generators : Fin 4 → Equiv.Perm (Fin 16) :=
  ![row16Generator0, row16Generator1, row16Generator2, row16Generator3]

abbrev Row16Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row16Generators)

noncomputable def row16 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row16Top

private def row17Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 2, 1, 3, 4, 6, 5, 7, 12, 14, 13, 15, 8, 10, 9, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 1, 3, 4, 6, 5, 7, 12, 14, 13, 15, 8, 10, 9, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row17Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 9, 11, 8, 10, 12, 13, 14, 15, 5, 7, 4, 6] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 14, 12, 15, 13, 6, 4, 7, 5, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row17Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 6, 5, 7, 0, 2, 1, 3, 12, 14, 15, 13, 8, 11, 9, 10] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 6, 5, 7, 0, 2, 1, 3, 12, 14, 15, 13, 8, 11, 9, 10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row17Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[10, 8, 9, 11, 12, 13, 15, 14, 1, 2, 0, 3, 4, 5, 7, 6] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 8, 9, 11, 12, 13, 15, 14, 1, 2, 0, 3, 4, 5, 7, 6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row17Generators : Fin 4 → Equiv.Perm (Fin 16) :=
  ![row17Generator0, row17Generator1, row17Generator2, row17Generator3]

abbrev Row17Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row17Generators)

noncomputable def row17 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row17Top

private def row18Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 2, 1, 3, 5, 7, 4, 6, 13, 15, 12, 14, 9, 11, 8, 10] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 1, 3, 6, 4, 7, 5, 14, 12, 15, 13, 10, 8, 11, 9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row18Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 10, 8, 11, 9, 12, 13, 14, 15, 5, 7, 4, 6] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 14, 12, 15, 13, 5, 7, 4, 6, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row18Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 6, 5, 7, 0, 2, 1, 3, 15, 13, 12, 14, 10, 9, 11, 8] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 6, 5, 7, 0, 2, 1, 3, 15, 13, 12, 14, 10, 9, 11, 8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row18Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9, 11, 10, 8, 12, 13, 15, 14, 1, 2, 0, 3, 5, 4, 6, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 8, 9, 11, 13, 12, 14, 15, 3, 0, 2, 1, 4, 5, 7, 6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row18Generators : Fin 4 → Equiv.Perm (Fin 16) :=
  ![row18Generator0, row18Generator1, row18Generator2, row18Generator3]

abbrev Row18Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row18Generators)

noncomputable def row18 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row18Top

private def row19Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 2, 1, 3, 5, 7, 4, 6, 13, 15, 12, 14, 9, 11, 8, 10] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 1, 3, 6, 4, 7, 5, 14, 12, 15, 13, 10, 8, 11, 9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row19Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 10, 8, 11, 9, 12, 13, 14, 15, 5, 7, 4, 6] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 14, 12, 15, 13, 5, 7, 4, 6, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row19Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 6, 5, 7, 0, 2, 1, 3, 13, 15, 14, 12, 11, 8, 10, 9] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 6, 5, 7, 0, 2, 1, 3, 13, 15, 14, 12, 11, 8, 10, 9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row19Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9, 11, 10, 8, 13, 12, 14, 15, 1, 2, 0, 3, 4, 5, 7, 6] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 8, 9, 11, 12, 13, 15, 14, 3, 0, 2, 1, 5, 4, 6, 7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row19Generators : Fin 4 → Equiv.Perm (Fin 16) :=
  ![row19Generator0, row19Generator1, row19Generator2, row19Generator3]

abbrev Row19Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row19Generators)

noncomputable def row19 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row19Top

private def row20Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 2, 1, 3, 4, 6, 5, 7, 12, 14, 13, 15, 8, 10, 9, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 1, 3, 4, 6, 5, 7, 12, 14, 13, 15, 8, 10, 9, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row20Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 10, 8, 11, 9, 15, 14, 13, 12, 6, 4, 7, 5] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 13, 15, 12, 14, 5, 7, 4, 6, 11, 10, 9, 8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row20Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 6, 5, 7, 0, 2, 1, 3, 14, 12, 13, 15, 9, 10, 8, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 6, 5, 7, 0, 2, 1, 3, 14, 12, 13, 15, 9, 10, 8, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row20Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[10, 8, 9, 11, 13, 12, 14, 15, 1, 2, 0, 3, 5, 4, 6, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 8, 9, 11, 13, 12, 14, 15, 1, 2, 0, 3, 5, 4, 6, 7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row20Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 9, 8, 11, 10, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[2, 3, 0, 1, 6, 7, 4, 5, 9, 8, 11, 10, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row20Generators : Fin 5 → Equiv.Perm (Fin 16) :=
  ![row20Generator0, row20Generator1, row20Generator2, row20Generator3, row20Generator4]

abbrev Row20Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row20Generators)

noncomputable def row20 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row20Top

private def row21Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 2, 1, 3, 4, 6, 5, 7, 12, 14, 13, 15, 8, 10, 9, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 1, 3, 4, 6, 5, 7, 12, 14, 13, 15, 8, 10, 9, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row21Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 9, 11, 8, 10, 12, 13, 14, 15, 5, 7, 4, 6] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 14, 12, 15, 13, 6, 4, 7, 5, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row21Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 6, 5, 7, 0, 2, 1, 3, 14, 12, 13, 15, 9, 10, 8, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 6, 5, 7, 0, 2, 1, 3, 14, 12, 13, 15, 9, 10, 8, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row21Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[10, 8, 9, 11, 13, 12, 14, 15, 1, 2, 0, 3, 5, 4, 6, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 8, 9, 11, 13, 12, 14, 15, 1, 2, 0, 3, 5, 4, 6, 7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row21Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[2, 3, 0, 1, 7, 6, 5, 4, 10, 11, 8, 9, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[2, 3, 0, 1, 7, 6, 5, 4, 10, 11, 8, 9, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row21Generators : Fin 5 → Equiv.Perm (Fin 16) :=
  ![row21Generator0, row21Generator1, row21Generator2, row21Generator3, row21Generator4]

abbrev Row21Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row21Generators)

noncomputable def row21 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row21Top

private def row22Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 2, 1, 3, 4, 6, 5, 7, 12, 14, 13, 15, 8, 10, 9, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 1, 3, 4, 6, 5, 7, 12, 14, 13, 15, 8, 10, 9, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row22Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 9, 11, 8, 10, 12, 13, 14, 15, 5, 7, 4, 6] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 14, 12, 15, 13, 6, 4, 7, 5, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row22Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 6, 5, 7, 0, 2, 1, 3, 12, 14, 15, 13, 8, 11, 9, 10] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 6, 5, 7, 0, 2, 1, 3, 12, 14, 15, 13, 8, 11, 9, 10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row22Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[8, 10, 11, 9, 14, 15, 13, 12, 1, 2, 0, 3, 5, 4, 6, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 8, 9, 11, 13, 12, 14, 15, 0, 3, 1, 2, 7, 6, 4, 5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row22Generators : Fin 4 → Equiv.Perm (Fin 16) :=
  ![row22Generator0, row22Generator1, row22Generator2, row22Generator3]

abbrev Row22Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row22Generators)

noncomputable def row22 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row22Top

private def row23Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 2, 1, 3, 4, 6, 5, 7, 12, 14, 13, 15, 8, 10, 9, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 1, 3, 4, 6, 5, 7, 12, 14, 13, 15, 8, 10, 9, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row23Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 9, 11, 8, 10, 13, 12, 15, 14, 4, 6, 5, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 12, 14, 13, 15, 6, 4, 7, 5, 9, 8, 11, 10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row23Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 6, 5, 7, 0, 2, 1, 3, 14, 12, 13, 15, 9, 10, 8, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 6, 5, 7, 0, 2, 1, 3, 14, 12, 13, 15, 9, 10, 8, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row23Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[10, 8, 9, 11, 13, 12, 14, 15, 1, 2, 0, 3, 5, 4, 6, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 8, 9, 11, 13, 12, 14, 15, 1, 2, 0, 3, 5, 4, 6, 7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row23Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[3, 2, 1, 0, 7, 6, 5, 4, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[3, 2, 1, 0, 7, 6, 5, 4, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row23Generators : Fin 5 → Equiv.Perm (Fin 16) :=
  ![row23Generator0, row23Generator1, row23Generator2, row23Generator3, row23Generator4]

abbrev Row23Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row23Generators)

noncomputable def row23 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row23Top

private def row24Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 2, 1, 3, 4, 6, 5, 7, 12, 14, 13, 15, 8, 10, 9, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 1, 3, 4, 6, 5, 7, 12, 14, 13, 15, 8, 10, 9, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row24Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 9, 11, 8, 10, 13, 12, 15, 14, 4, 6, 5, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 12, 14, 13, 15, 6, 4, 7, 5, 9, 8, 11, 10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row24Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 6, 5, 7, 0, 2, 1, 3, 12, 14, 15, 13, 9, 10, 8, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 6, 5, 7, 0, 2, 1, 3, 14, 12, 13, 15, 8, 11, 9, 10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row24Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[10, 8, 9, 11, 12, 13, 15, 14, 1, 2, 0, 3, 5, 4, 6, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 8, 9, 11, 13, 12, 14, 15, 1, 2, 0, 3, 4, 5, 7, 6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row24Generators : Fin 4 → Equiv.Perm (Fin 16) :=
  ![row24Generator0, row24Generator1, row24Generator2, row24Generator3]

abbrev Row24Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row24Generators)

noncomputable def row24 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row24Top

private def row25Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 2, 1, 3, 4, 6, 5, 7, 14, 12, 15, 13, 8, 10, 9, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 1, 3, 4, 6, 5, 7, 12, 14, 13, 15, 9, 11, 8, 10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row25Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 10, 8, 11, 9, 13, 12, 15, 14, 4, 6, 5, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 12, 14, 13, 15, 5, 7, 4, 6, 9, 8, 11, 10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row25Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 6, 5, 7, 0, 2, 1, 3, 15, 13, 12, 14, 10, 9, 11, 8] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 6, 5, 7, 0, 2, 1, 3, 15, 13, 12, 14, 10, 9, 11, 8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row25Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9, 11, 10, 8, 12, 13, 15, 14, 1, 2, 0, 3, 5, 4, 6, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 8, 9, 11, 13, 12, 14, 15, 3, 0, 2, 1, 4, 5, 7, 6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row25Generators : Fin 4 → Equiv.Perm (Fin 16) :=
  ![row25Generator0, row25Generator1, row25Generator2, row25Generator3]

abbrev Row25Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row25Generators)

noncomputable def row25 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row25Top

private def row26Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 2, 1, 3, 4, 6, 5, 7, 14, 12, 15, 13, 8, 10, 9, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 1, 3, 4, 6, 5, 7, 12, 14, 13, 15, 9, 11, 8, 10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row26Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 10, 8, 11, 9, 13, 12, 15, 14, 4, 6, 5, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 12, 14, 13, 15, 5, 7, 4, 6, 9, 8, 11, 10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row26Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 6, 5, 7, 0, 2, 1, 3, 13, 15, 14, 12, 10, 9, 11, 8] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 6, 5, 7, 0, 2, 1, 3, 15, 13, 12, 14, 11, 8, 10, 9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row26Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9, 11, 10, 8, 13, 12, 14, 15, 1, 2, 0, 3, 5, 4, 6, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 8, 9, 11, 13, 12, 14, 15, 3, 0, 2, 1, 5, 4, 6, 7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row26Generators : Fin 4 → Equiv.Perm (Fin 16) :=
  ![row26Generator0, row26Generator1, row26Generator2, row26Generator3]

abbrev Row26Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row26Generators)

noncomputable def row26 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row26Top

private def row27Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 2, 1, 3, 4, 6, 5, 7, 12, 14, 13, 15, 8, 10, 9, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 1, 3, 4, 6, 5, 7, 12, 14, 13, 15, 8, 10, 9, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row27Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 10, 8, 11, 9, 12, 13, 14, 15, 4, 6, 5, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 12, 14, 13, 15, 5, 7, 4, 6, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row27Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 6, 5, 7, 0, 2, 1, 3, 14, 12, 13, 15, 9, 10, 8, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 6, 5, 7, 0, 2, 1, 3, 14, 12, 13, 15, 9, 10, 8, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row27Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[10, 8, 9, 11, 13, 12, 14, 15, 1, 2, 0, 3, 5, 4, 6, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 8, 9, 11, 13, 12, 14, 15, 1, 2, 0, 3, 5, 4, 6, 7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row27Generators : Fin 4 → Equiv.Perm (Fin 16) :=
  ![row27Generator0, row27Generator1, row27Generator2, row27Generator3]

abbrev Row27Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row27Generators)

noncomputable def row27 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row27Top

private def row28Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 2, 1, 3, 4, 6, 5, 7, 12, 14, 13, 15, 8, 10, 9, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 1, 3, 4, 6, 5, 7, 12, 14, 13, 15, 8, 10, 9, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row28Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 10, 8, 11, 9, 12, 13, 14, 15, 4, 6, 5, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 12, 14, 13, 15, 5, 7, 4, 6, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row28Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 6, 5, 7, 0, 2, 1, 3, 12, 14, 15, 13, 9, 10, 8, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 6, 5, 7, 0, 2, 1, 3, 14, 12, 13, 15, 8, 11, 9, 10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row28Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[10, 8, 9, 11, 12, 13, 15, 14, 1, 2, 0, 3, 5, 4, 6, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 8, 9, 11, 13, 12, 14, 15, 1, 2, 0, 3, 4, 5, 7, 6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row28Generators : Fin 4 → Equiv.Perm (Fin 16) :=
  ![row28Generator0, row28Generator1, row28Generator2, row28Generator3]

abbrev Row28Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row28Generators)

noncomputable def row28 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row28Top

private def row29Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 2, 1, 3, 4, 6, 5, 7, 14, 12, 15, 13, 10, 8, 11, 9] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 1, 3, 4, 6, 5, 7, 13, 15, 12, 14, 9, 11, 8, 10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row29Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 8, 10, 9, 11, 12, 13, 14, 15, 4, 6, 5, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 12, 14, 13, 15, 4, 6, 5, 7, 8, 9, 10, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row29Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4, 6, 5, 7, 0, 2, 1, 3, 14, 12, 13, 15, 9, 10, 8, 11] : Array (Fin 16))[x.val]!
  invFun x := (#[4, 6, 5, 7, 0, 2, 1, 3, 14, 12, 13, 15, 9, 10, 8, 11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def row29Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[10, 8, 9, 11, 13, 12, 14, 15, 1, 2, 0, 3, 5, 4, 6, 7] : Array (Fin 16))[x.val]!
  invFun x := (#[10, 8, 9, 11, 13, 12, 14, 15, 1, 2, 0, 3, 5, 4, 6, 7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row29Generators : Fin 4 → Equiv.Perm (Fin 16) :=
  ![row29Generator0, row29Generator1, row29Generator2, row29Generator3]

abbrev Row29Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range row29Generators)

noncomputable def row29 : DegreeTwoPairTopFiniteInterface 16 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    Row29Top

noncomputable def interface : Fin 29 →
    DegreeTwoPairTopFiniteInterface 16 :=
  Fin.cases row1 <| Fin.cases row2 <| Fin.cases row3 <| Fin.cases row4 <| Fin.cases row5 <| Fin.cases row6 <| Fin.cases row7 <| Fin.cases row8 <| Fin.cases row9 <| Fin.cases row10 <| Fin.cases row11 <| Fin.cases row12 <| Fin.cases row13 <| Fin.cases row14 <| Fin.cases row15 <| Fin.cases row16 <| Fin.cases row17 <| Fin.cases row18 <| Fin.cases row19 <| Fin.cases row20 <| Fin.cases row21 <| Fin.cases row22 <| Fin.cases row23 <| Fin.cases row24 <| Fin.cases row25 <| Fin.cases row26 <| Fin.cases row27 <| Fin.cases row28 <| Fin.cases row29 Fin.elim0

end DegreeTwoZeroSixteenInterfaces
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
