import SymmetricSubgroupAsymptotics.CyclicFourAugmentationTranslations
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row62CyclicFourKernelModel
open CyclicFourAugmentationTranslations (Model Point)
def points : Point ≃ Fin 12 where
  toFun x := (#[0,4,8,3,7,11,6,10,2,9,1,5] : Array (Fin 12))[3*x.1.val+x.2.val]!
  invFun x := (#[(0,0),(3,1),(2,2),(1,0),(0,1),(3,2),
    (2,0),(1,1),(0,2),(3,0),(2,1),(1,2)] : Array Point)[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
abbrev action := CyclicFourAugmentationTranslations.action points
theorem action_injective : Function.Injective action :=
  CyclicFourAugmentationTranslations.action_injective points
end SymmetricSubgroupAsymptotics.Row62CyclicFourKernelModel
