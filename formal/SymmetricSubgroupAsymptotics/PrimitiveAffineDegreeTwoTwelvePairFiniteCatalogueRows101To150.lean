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

end DegreeTwoTwelvePairFiniteCatalogue
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
