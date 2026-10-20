import SymmetricSubgroupAsymptotics.BinaryPlaneThreeTranslations
import SymmetricSubgroupAsymptotics.Row27OriginalQuartetFrame
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row27BinaryPlaneKernelModel
open BinaryPlaneThreeTranslations (Plane Model Point)
private def planeLabel : Plane ≃ Fin 4 where
  toFun v := if v 0=0 then (if v 1=0 then 0 else 2) else (if v 1=0 then 1 else 3)
  invFun i := ![![0,0],![1,0],![0,1],![1,1]] i
  left_inv := by decide +kernel
  right_inv := by decide +kernel
 def points : Point ≃ Fin 12 :=
  ((Equiv.prodComm Plane (Fin 3)).trans
    (Equiv.prodCongr (Equiv.refl (Fin 3)) planeLabel)).trans Row27OriginalQuartetFrame.points
abbrev action := BinaryPlaneThreeTranslations.action points
 theorem action_injective : Function.Injective action :=
  BinaryPlaneThreeTranslations.action_injective points
end SymmetricSubgroupAsymptotics.Row27BinaryPlaneKernelModel
