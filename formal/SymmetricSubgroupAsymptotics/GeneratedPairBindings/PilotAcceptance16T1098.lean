import SymmetricSubgroupAsymptotics.BinaryPairSharedAcceptance
import SymmetricSubgroupAsymptotics.BinaryPairCentralKernel
import SymmetricSubgroupAsymptotics.GeneratedPairBindings.PilotBinding16T1098
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.GapsPilot077

/-! Complete coverage of every original normal by the shared independent
registries. The exceptional branch identifies the literal original normal
as its coordinate axis; no list of original normal lifts is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairAcceptance16T1098
open BinaryPairBinding16T1098
local instance : Group SourceTop := BinaryTopSource046.group

private theorem kernel_space : BinaryKernelAxes077.kernel.toSubmodule=physicalFrame.kernelSpace :=
  BinaryPairBinding16T1098.kernel_space.symm

private theorem cells (i : Fin 19) (j : Fin 19) :
    (BinaryTopRegistry046.states j).degree+
      BinaryPairFrame.sharedCost BinaryKernelAxes077.action BinaryKernelAxes077.states
        (fun i => BinaryKernelAxes077.states (BinaryKernelCuts077.cutIndex i))
        (fun i => BinaryKernelAxes077.states (BinaryKernelCuts077.fixedIndex i)) i<Nat.card (Fin 16) ∨
      BinaryKernelGaps077.exceptionalAxis i ∧ (BinaryTopRegistry046.states j).kernel=⊥ := by
  have hc : BinaryPairFrame.sharedCost BinaryKernelAxes077.action BinaryKernelAxes077.states
      (fun i => BinaryKernelAxes077.states (BinaryKernelCuts077.cutIndex i))
      (fun i => BinaryKernelAxes077.states (BinaryKernelCuts077.fixedIndex i)) i=BinaryKernelCuts077.cost i :=
    (BinaryKernelCuts077.cost_eq_actual_finranks i).symm
  simpa only [hc,Nat.card_eq_fintype_card,Fintype.card_fin] using
    BinaryKernelGaps077.gap_or_trivial_top i j

/-- Every actual original normal has a physical certificate of width 16,
or equals one of the explicit exceptional correlated flip axes. -/
theorem accepted_or_exceptional (N : Subgroup Original) [N.Normal] :
    (∃ C : BinaryPairLocalCertificate generators physicalFrame.top N,C.width=16) ∨
      ∃ i : Fin 19, BinaryKernelGaps077.exceptionalAxis i ∧
        N=physicalFrame.coordinateSubgroup (BinaryKernelAxes077.states i).toSubmodule := by
  have ht : ∀ T : Subgroup SourceTop,T.Normal → ∃ j,(BinaryTopRegistry046.states j).kernel=T := by
    intro T hT
    letI : T.Normal := hT
    exact BinaryTopRegistry046.complete T
  simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using
    physicalFrame.shared_complete_acceptance BinaryKernelAxes077.action topEquiv action_eq
      BinaryKernelAxes077.kernel kernel_space BinaryKernelAxes077.states
      (fun i => BinaryKernelAxes077.states (BinaryKernelCuts077.cutIndex i))
      (fun i => BinaryKernelAxes077.states (BinaryKernelCuts077.fixedIndex i)) BinaryKernelCuts077.certificate
      BinaryKernelAxes077.complete BinaryTopRegistry046.states ht BinaryKernelGaps077.exceptionalAxis cells generators N

/-- The selected faithful top cover always has even degree.  Retaining this
fact makes the resulting physical certificate directly admissible for the
even-marker recurrence. -/
theorem accepted_or_exceptional_even (N : Subgroup Original) [N.Normal] :
    (∃ C : BinaryPairLocalCertificate generators physicalFrame.top N,
      C.width=16 ∧ Even C.coverDegree) ∨
      ∃ i : Fin 19, BinaryKernelGaps077.exceptionalAxis i ∧
        N=physicalFrame.coordinateSubgroup (BinaryKernelAxes077.states i).toSubmodule := by
  have ht : ∀ T : Subgroup SourceTop,T.Normal → ∃ j,(BinaryTopRegistry046.states j).kernel=T := by
    intro T hT
    letI : T.Normal := hT
    exact BinaryTopRegistry046.complete T
  have heven : ∀ j : Fin 19, Even (BinaryTopRegistry046.states j).degree := by
    intro j
    revert j
    decide +kernel
  simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using
    physicalFrame.shared_complete_acceptance_with_cover_property
      BinaryKernelAxes077.action topEquiv action_eq BinaryKernelAxes077.kernel kernel_space
      BinaryKernelAxes077.states
      (fun i => BinaryKernelAxes077.states (BinaryKernelCuts077.cutIndex i))
      (fun i => BinaryKernelAxes077.states (BinaryKernelCuts077.fixedIndex i))
      BinaryKernelCuts077.certificate BinaryKernelAxes077.complete BinaryTopRegistry046.states ht
      Even heven BinaryKernelGaps077.exceptionalAxis cells generators N

end SymmetricSubgroupAsymptotics.BinaryPairAcceptance16T1098
