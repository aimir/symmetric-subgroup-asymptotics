import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.CutsPilot097

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryKernelGaps097
open BinaryKernelAxes097 BinaryKernelCuts097
local instance : Group Source := BinaryTopSource056.group

def exceptionalAxis (i : Fin 17) : Prop := i=2

instance (i : Fin 17) : Decidable (exceptionalAxis i) := by
  unfold exceptionalAxis
  infer_instance

/-- Every shared finite joint cell satisfies the gap or has trivial top;
compatibility is not needed for this stronger numerical assertion. -/
private theorem numerical : ∀ (i : Fin 17) (j : Fin 11),
    (BinaryTopRegistry056.states j).degree+cost i<16 ∨
      exceptionalAxis i ∧ j=0 := by decide +kernel

theorem bottom_kernel : (BinaryTopRegistry056.states 0).kernel=⊥ := by
  ext x
  exact ((BinaryTopRegistry056.states 0).mask_eq x).symm.trans
    (BinaryTopRegistry056.registry.bottom_mask x)

theorem gap_or_trivial_top (i : Fin 17) (j : Fin 11) :
    (BinaryTopRegistry056.states j).degree+cost i<16 ∨
      exceptionalAxis i ∧ (BinaryTopRegistry056.states j).kernel=⊥ := by
  rcases numerical i j with h|⟨h,rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨h,bottom_kernel⟩

theorem original_bottom_kernel : (BinaryTopRegistry056.originalStates 0).kernel=⊥ := by
  change ((BinaryTopRegistry056.states 0).transport BinaryTopSource056.originalEquiv).kernel=⊥
  rw [BinaryTopKernelData.transport_kernel,bottom_kernel,Subgroup.map_bot]

theorem gap_or_original_trivial_top (i : Fin 17) (j : Fin 11) :
    (BinaryTopRegistry056.originalStates j).degree+cost i<16 ∨
      exceptionalAxis i ∧ (BinaryTopRegistry056.originalStates j).kernel=⊥ := by
  rcases numerical i j with h|⟨h,rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨h,original_bottom_kernel⟩

/-- Independently complete invariant-axis and top-normal registries cover
all mathematical joint states, including every possible original lift. -/
theorem complete_joint_states (W : Subrepresentation action)
    (hW : W.toSubmodule≤kernel.toSubmodule) (N : Subgroup Source) [N.Normal] :
    ∃ i : Fin 17, ∃ j : Fin 11, states i=W ∧
      (BinaryTopRegistry056.states j).kernel=N ∧
      ((BinaryTopRegistry056.states j).degree+cost i<16 ∨
        exceptionalAxis i ∧ N=⊥) := by
  obtain ⟨i,hi⟩ := BinaryKernelAxes097.complete W hW
  obtain ⟨j,hj⟩ := BinaryTopRegistry056.complete N
  exact ⟨i,j,hi,hj,by simpa only [hj] using gap_or_trivial_top i j⟩
end SymmetricSubgroupAsymptotics.BinaryKernelGaps097

namespace SymmetricSubgroupAsymptotics.BinaryKernelCentral097
open BinaryKernelAxes097
local instance : Group Source := BinaryTopSource056.group

namespace Axis2
private def factorEntries (l : Fin 8) : List (Fin 2 × Fin 8) :=
  (if l.val < 4 then (if l.val < 2 then (if l.val < 1 then [(1,0)] else [(1,1)]) else (if l.val < 3 then [(1,0),(1,1)] else [])) else (if l.val < 6 then (if l.val < 5 then [] else []) else (if l.val < 7 then [] else [])))
private def factor : (Fin 2 → Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2) :=
  LinearMap.pi (fun l => ((factorEntries l).map
    (fun p => (LinearMap.proj p.2 : (Fin 8 → ZMod 2) →ₗ[ZMod 2] ZMod 2).comp
      (LinearMap.proj p.1 : (Fin 2 → Fin 8 → ZMod 2) →ₗ[ZMod 2]
        (Fin 8 → ZMod 2)))).sum)
private theorem fixed_le_kernel_basis : ∀ j,
    (charts 12).2.inclusion (Pi.single j 1)∈kernelChart.space := by decide +kernel
private theorem fixed_basis : ∀ j l,
    action (generators l) ((charts 12).2.inclusion (Pi.single j 1))-
      (charts 12).2.inclusion (Pi.single j 1)∈(charts 2).2.space := by
  simp only [action_numeric]
  decide +kernel
private theorem factor_basis : ∀ j,
    (charts 12).2.defect (kernelChart.inclusion (Pi.single j 1))=
      factor (binaryCoordinate_generatorDefects action generators (charts 2).2
        (kernelChart.inclusion (Pi.single j 1))) := by
  simp only [binaryCoordinate_generatorDefects_apply,action_numeric]
  decide +kernel
private theorem full_fixed : ∀ v : Fin 8 → ZMod 2,
    v∈(charts 12).2.space ↔ v∈kernelChart.space ∧
      ∀ j,action (generators j) v-v∈(charts 2).2.space :=
  binaryCoordinate_fixed_of_factor kernelChart (charts 2).2 (charts 12).2
    action generators factor fixed_le_kernel_basis fixed_basis factor_basis

/-- The full fixed preimage of the exceptional axis itself. -/
theorem certificate : BinaryCoordinateCutData action kernel (states 2) (states 2) (states 12) :=
  binaryCoordinate_cut_of_checks kernelChart (charts 2).2 (charts 2).2 (charts 12).2
    action kernel (states 2) (states 2) (states 12) rfl
    (states_space 2) (states_space 2) (states_space 12) generators generators_full
    (by decide +kernel) (by decide +kernel)
    (by simp only [action_numeric]; decide +kernel) full_fixed



theorem dimension : Module.finrank (ZMod 2) (states 12).toSubmodule-
    Module.finrank (ZMod 2) (states 2).toSubmodule=2 := by
  rw [states_space 12,states_space 2,(charts 12).2.finrank,(charts 2).2.finrank]
  decide +kernel
end Axis2
end SymmetricSubgroupAsymptotics.BinaryKernelCentral097
