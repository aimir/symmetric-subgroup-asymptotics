import SymmetricSubgroupAsymptotics.GeneratedPairBindings.PilotBinding16T1086Base

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairBinding16T1086
local instance pilotSourceMapGroup : Group SourceTop := BinaryTopSource056.group

def originalToShared : BinaryNormalGeneratorWords tops BinaryTopSource056.generators where
  words j := (if j.val < 2 then (if j.val < 1 then [] else []) else (if j.val < 3 then [0,1,1] else [1,1,1]))
  equations := by decide +kernel
def sharedToOriginal : BinaryNormalGeneratorWords BinaryTopSource056.generators tops where
  words j := (if j.val < 1 then [2,3,3] else [3,3,3])
  equations := by decide +kernel

theorem top_range : physicalFrame.top.range=Subgroup.closure (Set.range BinaryTopSource056.generators) := by
  change (BinaryPairFrame.ofGenerators frame BinaryActionData16.node1086Generators tops preserves).top.range=_
  rw [BinaryPairFrame.ofGenerators_top_range]
  exact le_antisymm originalToShared.closure_le sharedToOriginal.closure_le

def topEquiv : SourceTop ≃* physicalFrame.top.range :=
  BinaryTopSource056.originalEquiv.trans (MulEquiv.subgroupCongr top_range.symm)

theorem action_eq : ∀ g v, BinaryKernelAxes097.action g v=physicalFrame.coordinateTopAction (topEquiv g) v := by
  intro g v
  rfl

def sourceMap : Original →* SourceTop := topEquiv.symm.toMonoidHom.comp physicalFrame.top.rangeRestrict
theorem topEquiv_sourceMap (u : Original) : topEquiv (sourceMap u)=physicalFrame.top.rangeRestrict u :=
  topEquiv.apply_symm_apply _
def images (j : Fin 4) : SourceTop := ⟨(if j.val < 2 then (if j.val < 1 then 15 else 15) else (if j.val < 3 then 8 else 1))⟩
theorem images_checked : ∀ j, tops j=(BinaryTopSource056.originalEquiv (images j) : Equiv.Perm (Fin 8)) := by
  simp only [← BinaryKernelAxes097.rowPermutation_eq_original]
  decide +kernel
theorem sourceMap_generator (j : Fin 4) : sourceMap (generators j)=images j := by
  apply topEquiv.injective
  change topEquiv (topEquiv.symm (physicalFrame.top.rangeRestrict (generators j)))=_
  rw [topEquiv.apply_symm_apply]
  apply Subtype.ext
  change (BinaryPairFrame.ofGenerators frame BinaryActionData16.node1086Generators tops preserves).top
    ⟨BinaryActionData16.node1086Generators j,Subgroup.subset_closure ⟨j,rfl⟩⟩=_
  rw [BinaryPairFrame.ofGenerators_top_generator]
  exact images_checked j

theorem sourceMap_kernel : sourceMap.ker=physicalFrame.top.ker := by
  ext u
  change topEquiv.symm (physicalFrame.top.rangeRestrict u)=1 ↔ physicalFrame.top u=1
  constructor
  · intro hu
    have h := congrArg topEquiv hu
    simp only [topEquiv.apply_symm_apply,map_one] at h
    exact congrArg Subtype.val h
  · intro hu
    have h : physicalFrame.top.rangeRestrict u=1 := Subtype.ext hu
    rw [h,map_one]

end SymmetricSubgroupAsymptotics.BinaryPairBinding16T1086
