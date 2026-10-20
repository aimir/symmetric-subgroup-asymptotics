import SymmetricSubgroupAsymptotics.BinaryPairSharedAcceptance
import SymmetricSubgroupAsymptotics.BinaryPairCentralKernel
import SymmetricSubgroupAsymptotics.GeneratedPairBindings.PilotBinding16T1086
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.GapsPilot097

/-! Complete coverage of every original normal by the shared independent
registries. The exceptional branch identifies the literal original normal
as its coordinate axis; no list of original normal lifts is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairAcceptance16T1086
open BinaryPairBinding16T1086
local instance : Group SourceTop := BinaryTopSource056.group

private theorem kernel_space : BinaryKernelAxes097.kernel.toSubmodule=physicalFrame.kernelSpace :=
  BinaryPairBinding16T1086.kernel_space.symm

private theorem cells (i : Fin 17) (j : Fin 11) :
    (BinaryTopRegistry056.states j).degree+
      BinaryPairFrame.sharedCost BinaryKernelAxes097.action BinaryKernelAxes097.states
        (fun i => BinaryKernelAxes097.states (BinaryKernelCuts097.cutIndex i))
        (fun i => BinaryKernelAxes097.states (BinaryKernelCuts097.fixedIndex i)) i<Nat.card (Fin 16) ∨
      BinaryKernelGaps097.exceptionalAxis i ∧ (BinaryTopRegistry056.states j).kernel=⊥ := by
  have hc : BinaryPairFrame.sharedCost BinaryKernelAxes097.action BinaryKernelAxes097.states
      (fun i => BinaryKernelAxes097.states (BinaryKernelCuts097.cutIndex i))
      (fun i => BinaryKernelAxes097.states (BinaryKernelCuts097.fixedIndex i)) i=BinaryKernelCuts097.cost i :=
    (BinaryKernelCuts097.cost_eq_actual_finranks i).symm
  simpa only [hc,Nat.card_eq_fintype_card,Fintype.card_fin] using
    BinaryKernelGaps097.gap_or_trivial_top i j

/-- Every actual original normal has a physical certificate of width 16,
or equals one of the explicit exceptional correlated flip axes. -/
theorem accepted_or_exceptional (N : Subgroup Original) [N.Normal] :
    (∃ C : BinaryPairLocalCertificate generators physicalFrame.top N,C.width=16) ∨
      ∃ i : Fin 17, BinaryKernelGaps097.exceptionalAxis i ∧
        N=physicalFrame.coordinateSubgroup (BinaryKernelAxes097.states i).toSubmodule := by
  have ht : ∀ T : Subgroup SourceTop,T.Normal → ∃ j,(BinaryTopRegistry056.states j).kernel=T := by
    intro T hT
    letI : T.Normal := hT
    exact BinaryTopRegistry056.complete T
  simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using
    physicalFrame.shared_complete_acceptance BinaryKernelAxes097.action topEquiv action_eq
      BinaryKernelAxes097.kernel kernel_space BinaryKernelAxes097.states
      (fun i => BinaryKernelAxes097.states (BinaryKernelCuts097.cutIndex i))
      (fun i => BinaryKernelAxes097.states (BinaryKernelCuts097.fixedIndex i)) BinaryKernelCuts097.certificate
      BinaryKernelAxes097.complete BinaryTopRegistry056.states ht BinaryKernelGaps097.exceptionalAxis cells generators N

/-- The selected faithful top cover always has even degree.  This parity is
retained through the complete original-normal choice. -/
theorem accepted_or_exceptional_even (N : Subgroup Original) [N.Normal] :
    (∃ C : BinaryPairLocalCertificate generators physicalFrame.top N,
      C.width=16 ∧ Even C.coverDegree) ∨
      ∃ i : Fin 17, BinaryKernelGaps097.exceptionalAxis i ∧
        N=physicalFrame.coordinateSubgroup (BinaryKernelAxes097.states i).toSubmodule := by
  have ht : ∀ T : Subgroup SourceTop,T.Normal → ∃ j,(BinaryTopRegistry056.states j).kernel=T := by
    intro T hT
    letI : T.Normal := hT
    exact BinaryTopRegistry056.complete T
  have heven : ∀ j : Fin 11, Even (BinaryTopRegistry056.states j).degree := by
    intro j
    revert j
    decide +kernel
  simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using
    physicalFrame.shared_complete_acceptance_with_cover_property
      BinaryKernelAxes097.action topEquiv action_eq BinaryKernelAxes097.kernel kernel_space
      BinaryKernelAxes097.states
      (fun i => BinaryKernelAxes097.states (BinaryKernelCuts097.cutIndex i))
      (fun i => BinaryKernelAxes097.states (BinaryKernelCuts097.fixedIndex i))
      BinaryKernelCuts097.certificate BinaryKernelAxes097.complete BinaryTopRegistry056.states ht
      Even heven BinaryKernelGaps097.exceptionalAxis cells generators N

end SymmetricSubgroupAsymptotics.BinaryPairAcceptance16T1086
