import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.CutsPilot077

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryKernelGaps077
open BinaryKernelAxes077 BinaryKernelCuts077
local instance : Group Source := BinaryTopSource046.group

def exceptionalAxis (i : Fin 19) : Prop := False

instance (i : Fin 19) : Decidable (exceptionalAxis i) := by
  unfold exceptionalAxis
  infer_instance

/-- Every shared finite joint cell satisfies the gap or has trivial top;
compatibility is not needed for this stronger numerical assertion. -/
private theorem numerical : ∀ (i : Fin 19) (j : Fin 19),
    (BinaryTopRegistry046.states j).degree+cost i<16 ∨
      exceptionalAxis i ∧ j=0 := by decide +kernel

theorem bottom_kernel : (BinaryTopRegistry046.states 0).kernel=⊥ := by
  ext x
  exact ((BinaryTopRegistry046.states 0).mask_eq x).symm.trans
    (BinaryTopRegistry046.registry.bottom_mask x)

theorem gap_or_trivial_top (i : Fin 19) (j : Fin 19) :
    (BinaryTopRegistry046.states j).degree+cost i<16 ∨
      exceptionalAxis i ∧ (BinaryTopRegistry046.states j).kernel=⊥ := by
  rcases numerical i j with h|⟨h,rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨h,bottom_kernel⟩

theorem original_bottom_kernel : (BinaryTopRegistry046.originalStates 0).kernel=⊥ := by
  change ((BinaryTopRegistry046.states 0).transport BinaryTopSource046.originalEquiv).kernel=⊥
  rw [BinaryTopKernelData.transport_kernel,bottom_kernel,Subgroup.map_bot]

theorem gap_or_original_trivial_top (i : Fin 19) (j : Fin 19) :
    (BinaryTopRegistry046.originalStates j).degree+cost i<16 ∨
      exceptionalAxis i ∧ (BinaryTopRegistry046.originalStates j).kernel=⊥ := by
  rcases numerical i j with h|⟨h,rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨h,original_bottom_kernel⟩

/-- Independently complete invariant-axis and top-normal registries cover
all mathematical joint states, including every possible original lift. -/
theorem complete_joint_states (W : Subrepresentation action)
    (hW : W.toSubmodule≤kernel.toSubmodule) (N : Subgroup Source) [N.Normal] :
    ∃ i : Fin 19, ∃ j : Fin 19, states i=W ∧
      (BinaryTopRegistry046.states j).kernel=N ∧
      ((BinaryTopRegistry046.states j).degree+cost i<16 ∨
        exceptionalAxis i ∧ N=⊥) := by
  obtain ⟨i,hi⟩ := BinaryKernelAxes077.complete W hW
  obtain ⟨j,hj⟩ := BinaryTopRegistry046.complete N
  exact ⟨i,j,hi,hj,by simpa only [hj] using gap_or_trivial_top i j⟩
end SymmetricSubgroupAsymptotics.BinaryKernelGaps077
