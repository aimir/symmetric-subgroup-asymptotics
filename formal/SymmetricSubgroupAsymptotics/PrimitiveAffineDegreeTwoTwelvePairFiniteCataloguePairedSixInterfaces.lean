import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopCatalogues

/-! The two literal degree-six interfaces used by paired count-twelve rows. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelvePairFiniteCatalogue

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
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries PairedSix1Top

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
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries PairedSix2Top

noncomputable def pairedSix : Fin 2 → DegreeTwoPairTopFiniteInterface 6 :=
  Fin.cases pairedSix1Interface <| Fin.cases pairedSix2Interface Fin.elim0

end DegreeTwoTwelvePairFiniteCatalogue
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
