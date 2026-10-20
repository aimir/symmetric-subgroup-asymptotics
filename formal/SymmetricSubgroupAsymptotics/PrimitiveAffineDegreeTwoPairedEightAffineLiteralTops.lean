import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopInterface
import Mathlib.GroupTheory.Perm.Fin

/-! Literal binary affine tops, independent of the growing paired catalogue. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairedEightSharedTops

private def top18Generator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[0, 6, 1, 7, 2, 4, 3, 5] : Array (Fin 8))[x.val]!
  invFun x := (#[0, 2, 4, 6, 5, 7, 1, 3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def sharedInvolution : Equiv.Perm (Fin 8) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6] : Array (Fin 8))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def top18Generators : Fin 2 → Equiv.Perm (Fin 8) :=
  ![top18Generator0, sharedInvolution]

abbrev Top18 : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range top18Generators)

noncomputable def top18 : DegreeTwoPairTopFiniteInterface 8 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries Top18

private def top20Generator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[0, 2, 1, 3, 4, 6, 5, 7] : Array (Fin 8))[x.val]!
  invFun x := (#[0, 2, 1, 3, 4, 6, 5, 7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def top20Generators : Fin 3 → Equiv.Perm (Fin 8) :=
  ![top18Generator0, top20Generator1, sharedInvolution]

abbrev Top20 : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range top20Generators)

noncomputable def top20 : DegreeTwoPairTopFiniteInterface 8 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries Top20

end DegreeTwoPairedEightSharedTops
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
