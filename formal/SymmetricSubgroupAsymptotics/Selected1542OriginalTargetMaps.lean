import SymmetricSubgroupAsymptotics.Selected1542OriginalPreimageQuotientEquiv
import SymmetricSubgroupAsymptotics.Selected1542TargetCubicSurjective

/-! The checked graph map agrees with the literal original source words.
This binds later kernel certificates to the same actual cubic projection. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure

local instance : Fintype originalPreimage := Fintype.ofFinite _
local instance : originalPreimage.subtype.range.Normal := by
  rw [Subgroup.range_subtype]
  infer_instance

def targetStateElement (i : Fin 48) : literalTarget :=
  actualQuotientGraph.certificate.sourceElement i

theorem targetStateElement_val (i : Fin 48) :
    (targetStateElement i).val=targetState i := rfl

theorem originalToTarget_state (i : Fin 48) :
    originalToTarget (originalState i)=targetStateElement i := by
  apply originalQuotientEquiv.symm.injective
  change originalQuotientEquiv.symm
    (originalQuotientEquiv (QuotientGroup.mk' originalPreimage.subtype.range (originalState i)))=
      originalQuotientEquiv.symm (targetStateElement i)
  rw [originalQuotientEquiv.symm_apply_apply]
  exact (actualQuotientGraph.certificate.hom_sourceElement i).symm

theorem originalToTarget_source (j : Fin 3) : originalToTarget (source j)=targetSource j := by
  have hs := congrArg originalToTarget (actualQuotientGraph.step_source 0 j)
  have hk : originalToTarget
      (originalPreimage.subtype (actualQuotientGraph.step_residue 0 j))=1 := by
    apply MonoidHom.mem_ker.mp
    rw [originalToTarget_ker]
    exact (actualQuotientGraph.step_residue 0 j).property
  rw [map_mul,map_mul,hk,mul_one] at hs
  change originalToTarget (originalState (step 0 j))=
    originalToTarget (originalState 0)*originalToTarget (source j) at hs
  rw [originalToTarget_state,originalToTarget_state] at hs
  have hzero : targetStateElement 0=1 := by
    apply Subtype.ext
    exact actualQuotientGraph.identity_target
  rw [hzero,one_mul] at hs
  rw [←hs]
  apply Subtype.ext
  change targetState (step 0 j)=targetGenerators j
  have ht : targetState (step 0 j)=targetState 0*targetGenerators j := by
    apply Equiv.ext
    exact all_step_target 0 j
  have hz : targetState 0=1 := by
    apply Equiv.ext
    exact identity_target
  simpa only [hz,one_mul] using ht

def originalCubic : Original →* CyclicThree :=
  (ActualRepeatedAlternatingCentralCoordinates.top targetAlternating 0).comp originalToTarget

theorem originalCubic_surjective : Function.Surjective originalCubic :=
  target_top_surjective.comp originalToTarget_surjective

def originalBinaryKernel : Subgroup Original := originalCubic.ker

end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
