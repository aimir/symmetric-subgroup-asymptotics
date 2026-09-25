import SymmetricSubgroupAsymptotics.GeneratedNormal8.States8T15

/-! All original normal subgroups of 8T15, by checked central-involution
closure in the complete literal quotient rows. Acceptance is separate. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryNormal8T15
local instance : Group Source := BinaryMenuCayley8T15.group

private def child0 (z : N0.state.Row) : Fin 20 :=
  ((if z.index.val < 16 then (if z.index.val < 8 then (if z.index.val < 4 then (if z.index.val < 2 then (if z.index.val < 1 then 0 else 0) else (if z.index.val < 3 then 0 else 0)) else (if z.index.val < 6 then (if z.index.val < 5 then 0 else 0) else (if z.index.val < 7 then 0 else 0))) else (if z.index.val < 12 then (if z.index.val < 10 then (if z.index.val < 9 then 0 else 0) else (if z.index.val < 11 then 0 else 0)) else (if z.index.val < 14 then (if z.index.val < 13 then 0 else 0) else (if z.index.val < 15 then 0 else 0)))) else (if z.index.val < 24 then (if z.index.val < 20 then (if z.index.val < 18 then (if z.index.val < 17 then 0 else 0) else (if z.index.val < 19 then 0 else 0)) else (if z.index.val < 22 then (if z.index.val < 21 then 0 else 0) else (if z.index.val < 23 then 0 else 0))) else (if z.index.val < 28 then (if z.index.val < 26 then (if z.index.val < 25 then 1 else 0) else (if z.index.val < 27 then 0 else 0)) else (if z.index.val < 30 then (if z.index.val < 29 then 0 else 0) else (if z.index.val < 31 then 0 else 0))))) : Fin 20)

private theorem child0_generator_mem (z : N0.state.Row)
    (hz : N0.state.CentralInvolution generators_full z) :
    ∀ j, N0.normalGenerators j ∈ (states (child0 z)).kernel := by
  have ht := N0.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(0 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(1 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(2 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(3 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(4 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(5 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(6 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(7 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(8 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(9 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(10 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(11 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(12 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(13 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(14 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(15 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(16 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(17 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(18 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(19 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(20 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(21 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(22 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(23 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · intro j
    exact Fin.elim0 j
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(25 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(26 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(27 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(28 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(29 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(30 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(31 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)

private theorem child0_lift_mem (z : N0.state.Row)
    (hz : N0.state.CentralInvolution generators_full z) :
    N0.cosets.representatives z.index ∈ (states (child0 z)).kernel := by
  have ht := N0.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(0 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(1 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(2 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(3 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(4 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(5 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(6 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(7 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(8 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(9 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(10 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(11 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(12 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(13 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(14 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(15 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(16 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(17 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(18 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(19 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(20 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(21 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(22 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(23 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N0.cosets.representatives 24 ∈ N1.kernel
    have he : N0.cosets.representatives 24=
        (⟨N1.normalCertificate.rows 0⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N1.normalCertificate _
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(25 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(26 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(27 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(28 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(29 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(30 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(31 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)

private theorem child0_card (z : N0.state.Row)
    (hz : N0.state.CentralInvolution generators_full z) :
    Nat.card (states (child0 z)).kernel=Nat.card N0.kernel*2 := by
  have ht := N0.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(0 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(1 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(2 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(3 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(4 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(5 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(6 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(7 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(8 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(9 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(10 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(11 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(12 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(13 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(14 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(15 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(16 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(17 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(18 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(19 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(20 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(21 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(22 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(23 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N1.kernel=Nat.card N0.kernel*2
    rw [N1.kernel_card,N0.kernel_card]
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(25 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(26 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(27 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(28 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(29 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(30 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(31 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)

private def child1 (z : N1.state.Row) : Fin 20 :=
  ((if z.index.val < 8 then (if z.index.val < 4 then (if z.index.val < 2 then (if z.index.val < 1 then 0 else 0) else (if z.index.val < 3 then 3 else 0)) else (if z.index.val < 6 then (if z.index.val < 5 then 4 else 0) else (if z.index.val < 7 then 0 else 0))) else (if z.index.val < 12 then (if z.index.val < 10 then (if z.index.val < 9 then 0 else 0) else (if z.index.val < 11 then 2 else 0)) else (if z.index.val < 14 then (if z.index.val < 13 then 0 else 0) else (if z.index.val < 15 then 0 else 0)))) : Fin 20)

private theorem child1_generator_mem (z : N1.state.Row)
    (hz : N1.state.CentralInvolution generators_full z) :
    ∀ j, N1.normalGenerators j ∈ (states (child1 z)).kernel := by
  have ht := N1.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(0 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(1 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N1.normalGenerators j ∈ N3.kernel
    intro j
    have he : ∀ j : Fin 1, N1.normalGenerators j=
        (⟨N3.normalCertificate.rows ((0 : Fin 4))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N3.normalCertificate _
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(3 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N1.normalGenerators j ∈ N4.kernel
    intro j
    have he : ∀ j : Fin 1, N1.normalGenerators j=
        (⟨N4.normalCertificate.rows ((1 : Fin 4))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N4.normalCertificate _
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(5 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(6 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(7 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(8 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(9 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N1.normalGenerators j ∈ N2.kernel
    intro j
    have he : ∀ j : Fin 1, N1.normalGenerators j=
        (⟨N2.normalCertificate.rows ((1 : Fin 4))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N2.normalCertificate _
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(11 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(12 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(13 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(14 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(15 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)

private theorem child1_lift_mem (z : N1.state.Row)
    (hz : N1.state.CentralInvolution generators_full z) :
    N1.cosets.representatives z.index ∈ (states (child1 z)).kernel := by
  have ht := N1.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(0 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(1 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N1.cosets.representatives 2 ∈ N3.kernel
    have he : N1.cosets.representatives 2=
        (⟨N3.normalCertificate.rows 2⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N3.normalCertificate _
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(3 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N1.cosets.representatives 4 ∈ N4.kernel
    have he : N1.cosets.representatives 4=
        (⟨N4.normalCertificate.rows 0⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N4.normalCertificate _
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(5 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(6 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(7 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(8 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(9 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N1.cosets.representatives 10 ∈ N2.kernel
    have he : N1.cosets.representatives 10=
        (⟨N2.normalCertificate.rows 0⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N2.normalCertificate _
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(11 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(12 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(13 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(14 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(15 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)

private theorem child1_card (z : N1.state.Row)
    (hz : N1.state.CentralInvolution generators_full z) :
    Nat.card (states (child1 z)).kernel=Nat.card N1.kernel*2 := by
  have ht := N1.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(0 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(1 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N3.kernel=Nat.card N1.kernel*2
    rw [N3.kernel_card,N1.kernel_card]
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(3 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N4.kernel=Nat.card N1.kernel*2
    rw [N4.kernel_card,N1.kernel_card]
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(5 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(6 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(7 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(8 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(9 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N2.kernel=Nat.card N1.kernel*2
    rw [N2.kernel_card,N1.kernel_card]
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(11 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(12 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(13 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(14 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(15 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)

private def child2 (z : N2.state.Row) : Fin 20 :=
  ((if z.index.val < 4 then (if z.index.val < 2 then (if z.index.val < 1 then 0 else 0) else (if z.index.val < 3 then 10 else 0)) else (if z.index.val < 6 then (if z.index.val < 5 then 0 else 0) else (if z.index.val < 7 then 0 else 0))) : Fin 20)

private theorem child2_generator_mem (z : N2.state.Row)
    (hz : N2.state.CentralInvolution generators_full z) :
    ∀ j, N2.normalGenerators j ∈ (states (child2 z)).kernel := by
  have ht := N2.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N2.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N2.state.centralRowTests generators_full ⟨(1 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N2.normalGenerators j ∈ N10.kernel
    intro j
    have he : ∀ j : Fin 1, N2.normalGenerators j=
        (⟨N10.normalCertificate.rows ((4 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N10.normalCertificate _
  · have hf : ¬N2.state.centralRowTests generators_full ⟨(3 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N2.state.centralRowTests generators_full ⟨(4 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N2.state.centralRowTests generators_full ⟨(5 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N2.state.centralRowTests generators_full ⟨(6 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N2.state.centralRowTests generators_full ⟨(7 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)

private theorem child2_lift_mem (z : N2.state.Row)
    (hz : N2.state.CentralInvolution generators_full z) :
    N2.cosets.representatives z.index ∈ (states (child2 z)).kernel := by
  have ht := N2.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N2.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N2.state.centralRowTests generators_full ⟨(1 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N2.cosets.representatives 2 ∈ N10.kernel
    have he : N2.cosets.representatives 2=
        (⟨N10.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N10.normalCertificate _
  · have hf : ¬N2.state.centralRowTests generators_full ⟨(3 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N2.state.centralRowTests generators_full ⟨(4 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N2.state.centralRowTests generators_full ⟨(5 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N2.state.centralRowTests generators_full ⟨(6 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N2.state.centralRowTests generators_full ⟨(7 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)

private theorem child2_card (z : N2.state.Row)
    (hz : N2.state.CentralInvolution generators_full z) :
    Nat.card (states (child2 z)).kernel=Nat.card N2.kernel*2 := by
  have ht := N2.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N2.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N2.state.centralRowTests generators_full ⟨(1 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N10.kernel=Nat.card N2.kernel*2
    rw [N10.kernel_card,N2.kernel_card]
  · have hf : ¬N2.state.centralRowTests generators_full ⟨(3 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N2.state.centralRowTests generators_full ⟨(4 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N2.state.centralRowTests generators_full ⟨(5 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N2.state.centralRowTests generators_full ⟨(6 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N2.state.centralRowTests generators_full ⟨(7 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)

private def child3 (z : N3.state.Row) : Fin 20 :=
  ((if z.index.val < 4 then (if z.index.val < 2 then (if z.index.val < 1 then 0 else 0) else (if z.index.val < 3 then 0 else 10)) else (if z.index.val < 6 then (if z.index.val < 5 then 0 else 0) else (if z.index.val < 7 then 0 else 0))) : Fin 20)

private theorem child3_generator_mem (z : N3.state.Row)
    (hz : N3.state.CentralInvolution generators_full z) :
    ∀ j, N3.normalGenerators j ∈ (states (child3 z)).kernel := by
  have ht := N3.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N3.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N3.state.centralRowTests generators_full ⟨(1 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N3.state.centralRowTests generators_full ⟨(2 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N3.normalGenerators j ∈ N10.kernel
    intro j
    have he : ∀ j : Fin 2, N3.normalGenerators j=
        (⟨N10.normalCertificate.rows (((if j.val < 1 then 3 else 2) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N10.normalCertificate _
  · have hf : ¬N3.state.centralRowTests generators_full ⟨(4 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N3.state.centralRowTests generators_full ⟨(5 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N3.state.centralRowTests generators_full ⟨(6 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N3.state.centralRowTests generators_full ⟨(7 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)

private theorem child3_lift_mem (z : N3.state.Row)
    (hz : N3.state.CentralInvolution generators_full z) :
    N3.cosets.representatives z.index ∈ (states (child3 z)).kernel := by
  have ht := N3.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N3.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N3.state.centralRowTests generators_full ⟨(1 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N3.state.centralRowTests generators_full ⟨(2 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N3.cosets.representatives 3 ∈ N10.kernel
    have he : N3.cosets.representatives 3=
        (⟨N10.normalCertificate.rows 0⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N10.normalCertificate _
  · have hf : ¬N3.state.centralRowTests generators_full ⟨(4 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N3.state.centralRowTests generators_full ⟨(5 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N3.state.centralRowTests generators_full ⟨(6 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N3.state.centralRowTests generators_full ⟨(7 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)

private theorem child3_card (z : N3.state.Row)
    (hz : N3.state.CentralInvolution generators_full z) :
    Nat.card (states (child3 z)).kernel=Nat.card N3.kernel*2 := by
  have ht := N3.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N3.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N3.state.centralRowTests generators_full ⟨(1 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N3.state.centralRowTests generators_full ⟨(2 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N10.kernel=Nat.card N3.kernel*2
    rw [N10.kernel_card,N3.kernel_card]
  · have hf : ¬N3.state.centralRowTests generators_full ⟨(4 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N3.state.centralRowTests generators_full ⟨(5 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N3.state.centralRowTests generators_full ⟨(6 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · have hf : ¬N3.state.centralRowTests generators_full ⟨(7 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)

private def child4 (z : N4.state.Row) : Fin 20 :=
  ((if z.index.val < 4 then (if z.index.val < 2 then (if z.index.val < 1 then 0 else 15) else (if z.index.val < 3 then 10 else 7)) else (if z.index.val < 6 then (if z.index.val < 5 then 9 else 8) else (if z.index.val < 7 then 5 else 6))) : Fin 20)

private theorem child4_generator_mem (z : N4.state.Row)
    (hz : N4.state.CentralInvolution generators_full z) :
    ∀ j, N4.normalGenerators j ∈ (states (child4 z)).kernel := by
  have ht := N4.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N4.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N4.normalGenerators j ∈ N15.kernel
    intro j
    have he : ∀ j : Fin 1, N4.normalGenerators j=
        (⟨N15.normalCertificate.rows ((1 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N15.normalCertificate _
  · change ∀ j, N4.normalGenerators j ∈ N10.kernel
    intro j
    have he : ∀ j : Fin 1, N4.normalGenerators j=
        (⟨N10.normalCertificate.rows ((0 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N10.normalCertificate _
  · change ∀ j, N4.normalGenerators j ∈ N7.kernel
    intro j
    have he : ∀ j : Fin 1, N4.normalGenerators j=
        (⟨N7.normalCertificate.rows ((1 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N7.normalCertificate _
  · change ∀ j, N4.normalGenerators j ∈ N9.kernel
    intro j
    have he : ∀ j : Fin 1, N4.normalGenerators j=
        (⟨N9.normalCertificate.rows ((1 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N9.normalCertificate _
  · change ∀ j, N4.normalGenerators j ∈ N8.kernel
    intro j
    have he : ∀ j : Fin 1, N4.normalGenerators j=
        (⟨N8.normalCertificate.rows ((0 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N8.normalCertificate _
  · change ∀ j, N4.normalGenerators j ∈ N5.kernel
    intro j
    have he : ∀ j : Fin 1, N4.normalGenerators j=
        (⟨N5.normalCertificate.rows ((1 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N5.normalCertificate _
  · change ∀ j, N4.normalGenerators j ∈ N6.kernel
    intro j
    have he : ∀ j : Fin 1, N4.normalGenerators j=
        (⟨N6.normalCertificate.rows ((0 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N6.normalCertificate _

private theorem child4_lift_mem (z : N4.state.Row)
    (hz : N4.state.CentralInvolution generators_full z) :
    N4.cosets.representatives z.index ∈ (states (child4 z)).kernel := by
  have ht := N4.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N4.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N4.cosets.representatives 1 ∈ N15.kernel
    have he : N4.cosets.representatives 1=
        (⟨N15.normalCertificate.rows 0⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N15.normalCertificate _
  · change N4.cosets.representatives 2 ∈ N10.kernel
    have he : N4.cosets.representatives 2=
        (⟨N10.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N10.normalCertificate _
  · change N4.cosets.representatives 3 ∈ N7.kernel
    have he : N4.cosets.representatives 3=
        (⟨N7.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N7.normalCertificate _
  · change N4.cosets.representatives 4 ∈ N9.kernel
    have he : N4.cosets.representatives 4=
        (⟨N9.normalCertificate.rows 0⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N9.normalCertificate _
  · change N4.cosets.representatives 5 ∈ N8.kernel
    have he : N4.cosets.representatives 5=
        (⟨N8.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N8.normalCertificate _
  · change N4.cosets.representatives 6 ∈ N5.kernel
    have he : N4.cosets.representatives 6=
        (⟨N5.normalCertificate.rows 2⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N5.normalCertificate _
  · change N4.cosets.representatives 7 ∈ N6.kernel
    have he : N4.cosets.representatives 7=
        (⟨N6.normalCertificate.rows 2⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N6.normalCertificate _

private theorem child4_card (z : N4.state.Row)
    (hz : N4.state.CentralInvolution generators_full z) :
    Nat.card (states (child4 z)).kernel=Nat.card N4.kernel*2 := by
  have ht := N4.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N4.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N15.kernel=Nat.card N4.kernel*2
    rw [N15.kernel_card,N4.kernel_card]
  · change Nat.card N10.kernel=Nat.card N4.kernel*2
    rw [N10.kernel_card,N4.kernel_card]
  · change Nat.card N7.kernel=Nat.card N4.kernel*2
    rw [N7.kernel_card,N4.kernel_card]
  · change Nat.card N9.kernel=Nat.card N4.kernel*2
    rw [N9.kernel_card,N4.kernel_card]
  · change Nat.card N8.kernel=Nat.card N4.kernel*2
    rw [N8.kernel_card,N4.kernel_card]
  · change Nat.card N5.kernel=Nat.card N4.kernel*2
    rw [N5.kernel_card,N4.kernel_card]
  · change Nat.card N6.kernel=Nat.card N4.kernel*2
    rw [N6.kernel_card,N4.kernel_card]

private def child5 (z : N5.state.Row) : Fin 20 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 16) else (if z.index.val < 3 then 12 else 13)) : Fin 20)

private theorem child5_generator_mem (z : N5.state.Row)
    (hz : N5.state.CentralInvolution generators_full z) :
    ∀ j, N5.normalGenerators j ∈ (states (child5 z)).kernel := by
  have ht := N5.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N5.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N5.normalGenerators j ∈ N16.kernel
    intro j
    have he : ∀ j : Fin 2, N5.normalGenerators j=
        (⟨N16.normalCertificate.rows (((if j.val < 1 then 12 else 2) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N16.normalCertificate _
  · change ∀ j, N5.normalGenerators j ∈ N12.kernel
    intro j
    have he : ∀ j : Fin 2, N5.normalGenerators j=
        (⟨N12.normalCertificate.rows (((if j.val < 1 then 12 else 2) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N12.normalCertificate _
  · change ∀ j, N5.normalGenerators j ∈ N13.kernel
    intro j
    have he : ∀ j : Fin 2, N5.normalGenerators j=
        (⟨N13.normalCertificate.rows (((if j.val < 1 then 13 else 2) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N13.normalCertificate _

private theorem child5_lift_mem (z : N5.state.Row)
    (hz : N5.state.CentralInvolution generators_full z) :
    N5.cosets.representatives z.index ∈ (states (child5 z)).kernel := by
  have ht := N5.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N5.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N5.cosets.representatives 1 ∈ N16.kernel
    have he : N5.cosets.representatives 1=
        (⟨N16.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N16.normalCertificate _
  · change N5.cosets.representatives 2 ∈ N12.kernel
    have he : N5.cosets.representatives 2=
        (⟨N12.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N12.normalCertificate _
  · change N5.cosets.representatives 3 ∈ N13.kernel
    have he : N5.cosets.representatives 3=
        (⟨N13.normalCertificate.rows 0⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N13.normalCertificate _

private theorem child5_card (z : N5.state.Row)
    (hz : N5.state.CentralInvolution generators_full z) :
    Nat.card (states (child5 z)).kernel=Nat.card N5.kernel*2 := by
  have ht := N5.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N5.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N16.kernel=Nat.card N5.kernel*2
    rw [N16.kernel_card,N5.kernel_card]
  · change Nat.card N12.kernel=Nat.card N5.kernel*2
    rw [N12.kernel_card,N5.kernel_card]
  · change Nat.card N13.kernel=Nat.card N5.kernel*2
    rw [N13.kernel_card,N5.kernel_card]

private def child6 (z : N6.state.Row) : Fin 20 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 16) else (if z.index.val < 3 then 14 else 11)) : Fin 20)

private theorem child6_generator_mem (z : N6.state.Row)
    (hz : N6.state.CentralInvolution generators_full z) :
    ∀ j, N6.normalGenerators j ∈ (states (child6 z)).kernel := by
  have ht := N6.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N6.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N6.normalGenerators j ∈ N16.kernel
    intro j
    have he : ∀ j : Fin 2, N6.normalGenerators j=
        (⟨N16.normalCertificate.rows (((if j.val < 1 then 2 else 10) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N16.normalCertificate _
  · change ∀ j, N6.normalGenerators j ∈ N14.kernel
    intro j
    have he : ∀ j : Fin 2, N6.normalGenerators j=
        (⟨N14.normalCertificate.rows (((if j.val < 1 then 0 else 9) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N14.normalCertificate _
  · change ∀ j, N6.normalGenerators j ∈ N11.kernel
    intro j
    have he : ∀ j : Fin 2, N6.normalGenerators j=
        (⟨N11.normalCertificate.rows (((if j.val < 1 then 2 else 10) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N11.normalCertificate _

private theorem child6_lift_mem (z : N6.state.Row)
    (hz : N6.state.CentralInvolution generators_full z) :
    N6.cosets.representatives z.index ∈ (states (child6 z)).kernel := by
  have ht := N6.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N6.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N6.cosets.representatives 1 ∈ N16.kernel
    have he : N6.cosets.representatives 1=
        (⟨N16.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N16.normalCertificate _
  · change N6.cosets.representatives 2 ∈ N14.kernel
    have he : N6.cosets.representatives 2=
        (⟨N14.normalCertificate.rows 13⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N14.normalCertificate _
  · change N6.cosets.representatives 3 ∈ N11.kernel
    have he : N6.cosets.representatives 3=
        (⟨N11.normalCertificate.rows 13⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N11.normalCertificate _

private theorem child6_card (z : N6.state.Row)
    (hz : N6.state.CentralInvolution generators_full z) :
    Nat.card (states (child6 z)).kernel=Nat.card N6.kernel*2 := by
  have ht := N6.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N6.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N16.kernel=Nat.card N6.kernel*2
    rw [N16.kernel_card,N6.kernel_card]
  · change Nat.card N14.kernel=Nat.card N6.kernel*2
    rw [N14.kernel_card,N6.kernel_card]
  · change Nat.card N11.kernel=Nat.card N6.kernel*2
    rw [N11.kernel_card,N6.kernel_card]

private def child7 (z : N7.state.Row) : Fin 20 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 17) else (if z.index.val < 3 then 12 else 11)) : Fin 20)

private theorem child7_generator_mem (z : N7.state.Row)
    (hz : N7.state.CentralInvolution generators_full z) :
    ∀ j, N7.normalGenerators j ∈ (states (child7 z)).kernel := by
  have ht := N7.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N7.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N7.normalGenerators j ∈ N17.kernel
    intro j
    have he : ∀ j : Fin 2, N7.normalGenerators j=
        (⟨N17.normalCertificate.rows (((if j.val < 1 then 2 else 5) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N17.normalCertificate _
  · change ∀ j, N7.normalGenerators j ∈ N12.kernel
    intro j
    have he : ∀ j : Fin 2, N7.normalGenerators j=
        (⟨N12.normalCertificate.rows (((if j.val < 1 then 2 else 4) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N12.normalCertificate _
  · change ∀ j, N7.normalGenerators j ∈ N11.kernel
    intro j
    have he : ∀ j : Fin 2, N7.normalGenerators j=
        (⟨N11.normalCertificate.rows (((if j.val < 1 then 2 else 4) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N11.normalCertificate _

private theorem child7_lift_mem (z : N7.state.Row)
    (hz : N7.state.CentralInvolution generators_full z) :
    N7.cosets.representatives z.index ∈ (states (child7 z)).kernel := by
  have ht := N7.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N7.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N7.cosets.representatives 1 ∈ N17.kernel
    have he : N7.cosets.representatives 1=
        (⟨N17.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N17.normalCertificate _
  · change N7.cosets.representatives 2 ∈ N12.kernel
    have he : N7.cosets.representatives 2=
        (⟨N12.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N12.normalCertificate _
  · change N7.cosets.representatives 3 ∈ N11.kernel
    have he : N7.cosets.representatives 3=
        (⟨N11.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N11.normalCertificate _

private theorem child7_card (z : N7.state.Row)
    (hz : N7.state.CentralInvolution generators_full z) :
    Nat.card (states (child7 z)).kernel=Nat.card N7.kernel*2 := by
  have ht := N7.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N7.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N17.kernel=Nat.card N7.kernel*2
    rw [N17.kernel_card,N7.kernel_card]
  · change Nat.card N12.kernel=Nat.card N7.kernel*2
    rw [N12.kernel_card,N7.kernel_card]
  · change Nat.card N11.kernel=Nat.card N7.kernel*2
    rw [N11.kernel_card,N7.kernel_card]

private def child8 (z : N8.state.Row) : Fin 20 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 17) else (if z.index.val < 3 then 14 else 13)) : Fin 20)

private theorem child8_generator_mem (z : N8.state.Row)
    (hz : N8.state.CentralInvolution generators_full z) :
    ∀ j, N8.normalGenerators j ∈ (states (child8 z)).kernel := by
  have ht := N8.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N8.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N8.normalGenerators j ∈ N17.kernel
    intro j
    have he : ∀ j : Fin 2, N8.normalGenerators j=
        (⟨N17.normalCertificate.rows (((if j.val < 1 then 2 else 3) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N17.normalCertificate _
  · change ∀ j, N8.normalGenerators j ∈ N14.kernel
    intro j
    have he : ∀ j : Fin 2, N8.normalGenerators j=
        (⟨N14.normalCertificate.rows (((if j.val < 1 then 0 else 1) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N14.normalCertificate _
  · change ∀ j, N8.normalGenerators j ∈ N13.kernel
    intro j
    have he : ∀ j : Fin 2, N8.normalGenerators j=
        (⟨N13.normalCertificate.rows (((if j.val < 1 then 2 else 3) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N13.normalCertificate _

private theorem child8_lift_mem (z : N8.state.Row)
    (hz : N8.state.CentralInvolution generators_full z) :
    N8.cosets.representatives z.index ∈ (states (child8 z)).kernel := by
  have ht := N8.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N8.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N8.cosets.representatives 1 ∈ N17.kernel
    have he : N8.cosets.representatives 1=
        (⟨N17.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N17.normalCertificate _
  · change N8.cosets.representatives 2 ∈ N14.kernel
    have he : N8.cosets.representatives 2=
        (⟨N14.normalCertificate.rows 13⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N14.normalCertificate _
  · change N8.cosets.representatives 3 ∈ N13.kernel
    have he : N8.cosets.representatives 3=
        (⟨N13.normalCertificate.rows 0⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N13.normalCertificate _

private theorem child8_card (z : N8.state.Row)
    (hz : N8.state.CentralInvolution generators_full z) :
    Nat.card (states (child8 z)).kernel=Nat.card N8.kernel*2 := by
  have ht := N8.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N8.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N17.kernel=Nat.card N8.kernel*2
    rw [N17.kernel_card,N8.kernel_card]
  · change Nat.card N14.kernel=Nat.card N8.kernel*2
    rw [N14.kernel_card,N8.kernel_card]
  · change Nat.card N13.kernel=Nat.card N8.kernel*2
    rw [N13.kernel_card,N8.kernel_card]

private def child9 (z : N9.state.Row) : Fin 20 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 18) else (if z.index.val < 3 then 11 else 13)) : Fin 20)

private theorem child9_generator_mem (z : N9.state.Row)
    (hz : N9.state.CentralInvolution generators_full z) :
    ∀ j, N9.normalGenerators j ∈ (states (child9 z)).kernel := by
  have ht := N9.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N9.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N9.normalGenerators j ∈ N18.kernel
    intro j
    have he : ∀ j : Fin 1, N9.normalGenerators j=
        (⟨N18.normalCertificate.rows ((9 : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N18.normalCertificate _
  · change ∀ j, N9.normalGenerators j ∈ N11.kernel
    intro j
    have he : ∀ j : Fin 1, N9.normalGenerators j=
        (⟨N11.normalCertificate.rows ((9 : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N11.normalCertificate _
  · change ∀ j, N9.normalGenerators j ∈ N13.kernel
    intro j
    have he : ∀ j : Fin 1, N9.normalGenerators j=
        (⟨N13.normalCertificate.rows ((9 : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N13.normalCertificate _

private theorem child9_lift_mem (z : N9.state.Row)
    (hz : N9.state.CentralInvolution generators_full z) :
    N9.cosets.representatives z.index ∈ (states (child9 z)).kernel := by
  have ht := N9.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N9.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N9.cosets.representatives 1 ∈ N18.kernel
    have he : N9.cosets.representatives 1=
        (⟨N18.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N18.normalCertificate _
  · change N9.cosets.representatives 2 ∈ N11.kernel
    have he : N9.cosets.representatives 2=
        (⟨N11.normalCertificate.rows 13⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N11.normalCertificate _
  · change N9.cosets.representatives 3 ∈ N13.kernel
    have he : N9.cosets.representatives 3=
        (⟨N13.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N13.normalCertificate _

private theorem child9_card (z : N9.state.Row)
    (hz : N9.state.CentralInvolution generators_full z) :
    Nat.card (states (child9 z)).kernel=Nat.card N9.kernel*2 := by
  have ht := N9.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N9.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N18.kernel=Nat.card N9.kernel*2
    rw [N18.kernel_card,N9.kernel_card]
  · change Nat.card N11.kernel=Nat.card N9.kernel*2
    rw [N11.kernel_card,N9.kernel_card]
  · change Nat.card N13.kernel=Nat.card N9.kernel*2
    rw [N13.kernel_card,N9.kernel_card]

private def child10 (z : N10.state.Row) : Fin 20 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 18) else (if z.index.val < 3 then 12 else 14)) : Fin 20)

private theorem child10_generator_mem (z : N10.state.Row)
    (hz : N10.state.CentralInvolution generators_full z) :
    ∀ j, N10.normalGenerators j ∈ (states (child10 z)).kernel := by
  have ht := N10.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N10.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N10.normalGenerators j ∈ N18.kernel
    intro j
    have he : ∀ j : Fin 2, N10.normalGenerators j=
        (⟨N18.normalCertificate.rows (((if j.val < 1 then 2 else 7) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N18.normalCertificate _
  · change ∀ j, N10.normalGenerators j ∈ N12.kernel
    intro j
    have he : ∀ j : Fin 2, N10.normalGenerators j=
        (⟨N12.normalCertificate.rows (((if j.val < 1 then 2 else 7) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N12.normalCertificate _
  · change ∀ j, N10.normalGenerators j ∈ N14.kernel
    intro j
    have he : ∀ j : Fin 2, N10.normalGenerators j=
        (⟨N14.normalCertificate.rows (((if j.val < 1 then 0 else 7) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N14.normalCertificate _

private theorem child10_lift_mem (z : N10.state.Row)
    (hz : N10.state.CentralInvolution generators_full z) :
    N10.cosets.representatives z.index ∈ (states (child10 z)).kernel := by
  have ht := N10.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N10.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N10.cosets.representatives 1 ∈ N18.kernel
    have he : N10.cosets.representatives 1=
        (⟨N18.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N18.normalCertificate _
  · change N10.cosets.representatives 2 ∈ N12.kernel
    have he : N10.cosets.representatives 2=
        (⟨N12.normalCertificate.rows 13⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N12.normalCertificate _
  · change N10.cosets.representatives 3 ∈ N14.kernel
    have he : N10.cosets.representatives 3=
        (⟨N14.normalCertificate.rows 12⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N14.normalCertificate _

private theorem child10_card (z : N10.state.Row)
    (hz : N10.state.CentralInvolution generators_full z) :
    Nat.card (states (child10 z)).kernel=Nat.card N10.kernel*2 := by
  have ht := N10.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N10.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N18.kernel=Nat.card N10.kernel*2
    rw [N18.kernel_card,N10.kernel_card]
  · change Nat.card N12.kernel=Nat.card N10.kernel*2
    rw [N12.kernel_card,N10.kernel_card]
  · change Nat.card N14.kernel=Nat.card N10.kernel*2
    rw [N14.kernel_card,N10.kernel_card]

private def child11 (z : N11.state.Row) : Fin 20 :=
  ((if z.index.val < 1 then 0 else 19) : Fin 20)

private theorem child11_generator_mem (z : N11.state.Row)
    (hz : N11.state.CentralInvolution generators_full z) :
    ∀ j, N11.normalGenerators j ∈ (states (child11 z)).kernel := by
  have ht := N11.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N11.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N11.normalGenerators j ∈ N19.kernel
    intro j
    have he : ∀ j : Fin 2, N11.normalGenerators j=
        (⟨N19.normalCertificate.rows (((if j.val < 1 then 19 else 9) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N19.normalCertificate _

private theorem child11_lift_mem (z : N11.state.Row)
    (hz : N11.state.CentralInvolution generators_full z) :
    N11.cosets.representatives z.index ∈ (states (child11 z)).kernel := by
  have ht := N11.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N11.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N11.cosets.representatives 1 ∈ N19.kernel
    have he : N11.cosets.representatives 1=
        (⟨N19.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N19.normalCertificate _

private theorem child11_card (z : N11.state.Row)
    (hz : N11.state.CentralInvolution generators_full z) :
    Nat.card (states (child11 z)).kernel=Nat.card N11.kernel*2 := by
  have ht := N11.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N11.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N19.kernel=Nat.card N11.kernel*2
    rw [N19.kernel_card,N11.kernel_card]

private def child12 (z : N12.state.Row) : Fin 20 :=
  ((if z.index.val < 1 then 0 else 19) : Fin 20)

private theorem child12_generator_mem (z : N12.state.Row)
    (hz : N12.state.CentralInvolution generators_full z) :
    ∀ j, N12.normalGenerators j ∈ (states (child12 z)).kernel := by
  have ht := N12.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N12.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N12.normalGenerators j ∈ N19.kernel
    intro j
    have he : ∀ j : Fin 3, N12.normalGenerators j=
        (⟨N19.normalCertificate.rows (((if j.val < 1 then 4 else (if j.val < 2 then 15 else 9)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N19.normalCertificate _

private theorem child12_lift_mem (z : N12.state.Row)
    (hz : N12.state.CentralInvolution generators_full z) :
    N12.cosets.representatives z.index ∈ (states (child12 z)).kernel := by
  have ht := N12.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N12.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N12.cosets.representatives 1 ∈ N19.kernel
    have he : N12.cosets.representatives 1=
        (⟨N19.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N19.normalCertificate _

private theorem child12_card (z : N12.state.Row)
    (hz : N12.state.CentralInvolution generators_full z) :
    Nat.card (states (child12 z)).kernel=Nat.card N12.kernel*2 := by
  have ht := N12.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N12.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N19.kernel=Nat.card N12.kernel*2
    rw [N19.kernel_card,N12.kernel_card]

private def child13 (z : N13.state.Row) : Fin 20 :=
  ((if z.index.val < 1 then 0 else 19) : Fin 20)

private theorem child13_generator_mem (z : N13.state.Row)
    (hz : N13.state.CentralInvolution generators_full z) :
    ∀ j, N13.normalGenerators j ∈ (states (child13 z)).kernel := by
  have ht := N13.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N13.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N13.normalGenerators j ∈ N19.kernel
    intro j
    have he : ∀ j : Fin 2, N13.normalGenerators j=
        (⟨N19.normalCertificate.rows (((if j.val < 1 then 19 else 5) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N19.normalCertificate _

private theorem child13_lift_mem (z : N13.state.Row)
    (hz : N13.state.CentralInvolution generators_full z) :
    N13.cosets.representatives z.index ∈ (states (child13 z)).kernel := by
  have ht := N13.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N13.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N13.cosets.representatives 1 ∈ N19.kernel
    have he : N13.cosets.representatives 1=
        (⟨N19.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N19.normalCertificate _

private theorem child13_card (z : N13.state.Row)
    (hz : N13.state.CentralInvolution generators_full z) :
    Nat.card (states (child13 z)).kernel=Nat.card N13.kernel*2 := by
  have ht := N13.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N13.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N19.kernel=Nat.card N13.kernel*2
    rw [N19.kernel_card,N13.kernel_card]

private def child14 (z : N14.state.Row) : Fin 20 :=
  ((if z.index.val < 1 then 0 else 19) : Fin 20)

private theorem child14_generator_mem (z : N14.state.Row)
    (hz : N14.state.CentralInvolution generators_full z) :
    ∀ j, N14.normalGenerators j ∈ (states (child14 z)).kernel := by
  have ht := N14.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N14.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N14.normalGenerators j ∈ N19.kernel
    intro j
    have he : ∀ j : Fin 3, N14.normalGenerators j=
        (⟨N19.normalCertificate.rows (((if j.val < 1 then 4 else (if j.val < 2 then 15 else 5)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N19.normalCertificate _

private theorem child14_lift_mem (z : N14.state.Row)
    (hz : N14.state.CentralInvolution generators_full z) :
    N14.cosets.representatives z.index ∈ (states (child14 z)).kernel := by
  have ht := N14.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N14.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N14.cosets.representatives 1 ∈ N19.kernel
    have he : N14.cosets.representatives 1=
        (⟨N19.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N19.normalCertificate _

private theorem child14_card (z : N14.state.Row)
    (hz : N14.state.CentralInvolution generators_full z) :
    Nat.card (states (child14 z)).kernel=Nat.card N14.kernel*2 := by
  have ht := N14.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N14.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N19.kernel=Nat.card N14.kernel*2
    rw [N19.kernel_card,N14.kernel_card]

private def child15 (z : N15.state.Row) : Fin 20 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 18) else (if z.index.val < 3 then 17 else 16)) : Fin 20)

private theorem child15_generator_mem (z : N15.state.Row)
    (hz : N15.state.CentralInvolution generators_full z) :
    ∀ j, N15.normalGenerators j ∈ (states (child15 z)).kernel := by
  have ht := N15.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N15.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N15.normalGenerators j ∈ N18.kernel
    intro j
    have he : ∀ j : Fin 1, N15.normalGenerators j=
        (⟨N18.normalCertificate.rows ((1 : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N18.normalCertificate _
  · change ∀ j, N15.normalGenerators j ∈ N17.kernel
    intro j
    have he : ∀ j : Fin 1, N15.normalGenerators j=
        (⟨N17.normalCertificate.rows ((1 : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N17.normalCertificate _
  · change ∀ j, N15.normalGenerators j ∈ N16.kernel
    intro j
    have he : ∀ j : Fin 1, N15.normalGenerators j=
        (⟨N16.normalCertificate.rows ((1 : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N16.normalCertificate _

private theorem child15_lift_mem (z : N15.state.Row)
    (hz : N15.state.CentralInvolution generators_full z) :
    N15.cosets.representatives z.index ∈ (states (child15 z)).kernel := by
  have ht := N15.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N15.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N15.cosets.representatives 1 ∈ N18.kernel
    have he : N15.cosets.representatives 1=
        (⟨N18.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N18.normalCertificate _
  · change N15.cosets.representatives 2 ∈ N17.kernel
    have he : N15.cosets.representatives 2=
        (⟨N17.normalCertificate.rows 13⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N17.normalCertificate _
  · change N15.cosets.representatives 3 ∈ N16.kernel
    have he : N15.cosets.representatives 3=
        (⟨N16.normalCertificate.rows 5⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N16.normalCertificate _

private theorem child15_card (z : N15.state.Row)
    (hz : N15.state.CentralInvolution generators_full z) :
    Nat.card (states (child15 z)).kernel=Nat.card N15.kernel*2 := by
  have ht := N15.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N15.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N18.kernel=Nat.card N15.kernel*2
    rw [N18.kernel_card,N15.kernel_card]
  · change Nat.card N17.kernel=Nat.card N15.kernel*2
    rw [N17.kernel_card,N15.kernel_card]
  · change Nat.card N16.kernel=Nat.card N15.kernel*2
    rw [N16.kernel_card,N15.kernel_card]

private def child16 (z : N16.state.Row) : Fin 20 :=
  ((if z.index.val < 1 then 0 else 19) : Fin 20)

private theorem child16_generator_mem (z : N16.state.Row)
    (hz : N16.state.CentralInvolution generators_full z) :
    ∀ j, N16.normalGenerators j ∈ (states (child16 z)).kernel := by
  have ht := N16.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N16.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N16.normalGenerators j ∈ N19.kernel
    intro j
    have he : ∀ j : Fin 2, N16.normalGenerators j=
        (⟨N19.normalCertificate.rows (((if j.val < 1 then 3 else 21) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N19.normalCertificate _

private theorem child16_lift_mem (z : N16.state.Row)
    (hz : N16.state.CentralInvolution generators_full z) :
    N16.cosets.representatives z.index ∈ (states (child16 z)).kernel := by
  have ht := N16.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N16.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N16.cosets.representatives 1 ∈ N19.kernel
    have he : N16.cosets.representatives 1=
        (⟨N19.normalCertificate.rows 29⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N19.normalCertificate _

private theorem child16_card (z : N16.state.Row)
    (hz : N16.state.CentralInvolution generators_full z) :
    Nat.card (states (child16 z)).kernel=Nat.card N16.kernel*2 := by
  have ht := N16.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N16.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N19.kernel=Nat.card N16.kernel*2
    rw [N19.kernel_card,N16.kernel_card]

private def child17 (z : N17.state.Row) : Fin 20 :=
  ((if z.index.val < 1 then 0 else 19) : Fin 20)

private theorem child17_generator_mem (z : N17.state.Row)
    (hz : N17.state.CentralInvolution generators_full z) :
    ∀ j, N17.normalGenerators j ∈ (states (child17 z)).kernel := by
  have ht := N17.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N17.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N17.normalGenerators j ∈ N19.kernel
    intro j
    have he : ∀ j : Fin 2, N17.normalGenerators j=
        (⟨N19.normalCertificate.rows (((if j.val < 1 then 3 else 5) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N19.normalCertificate _

private theorem child17_lift_mem (z : N17.state.Row)
    (hz : N17.state.CentralInvolution generators_full z) :
    N17.cosets.representatives z.index ∈ (states (child17 z)).kernel := by
  have ht := N17.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N17.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N17.cosets.representatives 1 ∈ N19.kernel
    have he : N17.cosets.representatives 1=
        (⟨N19.normalCertificate.rows 29⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N19.normalCertificate _

private theorem child17_card (z : N17.state.Row)
    (hz : N17.state.CentralInvolution generators_full z) :
    Nat.card (states (child17 z)).kernel=Nat.card N17.kernel*2 := by
  have ht := N17.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N17.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N19.kernel=Nat.card N17.kernel*2
    rw [N19.kernel_card,N17.kernel_card]

private def child18 (z : N18.state.Row) : Fin 20 :=
  ((if z.index.val < 1 then 0 else 19) : Fin 20)

private theorem child18_generator_mem (z : N18.state.Row)
    (hz : N18.state.CentralInvolution generators_full z) :
    ∀ j, N18.normalGenerators j ∈ (states (child18 z)).kernel := by
  have ht := N18.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N18.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N18.normalGenerators j ∈ N19.kernel
    intro j
    have he : ∀ j : Fin 2, N18.normalGenerators j=
        (⟨N19.normalCertificate.rows (((if j.val < 1 then 3 else 15) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N19.normalCertificate _

private theorem child18_lift_mem (z : N18.state.Row)
    (hz : N18.state.CentralInvolution generators_full z) :
    N18.cosets.representatives z.index ∈ (states (child18 z)).kernel := by
  have ht := N18.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N18.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N18.cosets.representatives 1 ∈ N19.kernel
    have he : N18.cosets.representatives 1=
        (⟨N19.normalCertificate.rows 27⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N19.normalCertificate _

private theorem child18_card (z : N18.state.Row)
    (hz : N18.state.CentralInvolution generators_full z) :
    Nat.card (states (child18 z)).kernel=Nat.card N18.kernel*2 := by
  have ht := N18.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N18.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N19.kernel=Nat.card N18.kernel*2
    rw [N19.kernel_card,N18.kernel_card]

private def child19 (z : N19.state.Row) : Fin 20 :=
  (0 : Fin 20)

private theorem child19_generator_mem (z : N19.state.Row)
    (hz : N19.state.CentralInvolution generators_full z) :
    ∀ j, N19.normalGenerators j ∈ (states (child19 z)).kernel := by
  have ht := N19.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N19.state.centralRowTests generators_full ⟨(0 : Fin 1)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)

private theorem child19_lift_mem (z : N19.state.Row)
    (hz : N19.state.CentralInvolution generators_full z) :
    N19.cosets.representatives z.index ∈ (states (child19 z)).kernel := by
  have ht := N19.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N19.state.centralRowTests generators_full ⟨(0 : Fin 1)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)

private theorem child19_card (z : N19.state.Row)
    (hz : N19.state.CentralInvolution generators_full z) :
    Nat.card (states (child19 z)).kernel=Nat.card N19.kernel*2 := by
  have ht := N19.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N19.state.centralRowTests generators_full ⟨(0 : Fin 1)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)

private def child : (i : Fin 20) → (states i).Row → Fin 20 :=
  (Fin.cases child0 (Fin.cases child1 (Fin.cases child2 (Fin.cases child3 (Fin.cases child4 (Fin.cases child5 (Fin.cases child6 (Fin.cases child7 (Fin.cases child8 (Fin.cases child9 (Fin.cases child10 (Fin.cases child11 (Fin.cases child12 (Fin.cases child13 (Fin.cases child14 (Fin.cases child15 (Fin.cases child16 (Fin.cases child17 (Fin.cases child18 (Fin.cases child19 (fun i => Fin.elim0 i)))))))))))))))))))))

def registry : BinaryNormalRegistry generators generators_full states where
  bottom := 0
  bottom_kernel := by
    change Subgroup.closure (Set.range N0.normalGenerators)=⊥
    rw [show Set.range N0.normalGenerators=∅ by ext x; simp]
    exact Subgroup.closure_empty
  child := child
  generator_mem := by
    intro i
    fin_cases i
    · exact child0_generator_mem
    · exact child1_generator_mem
    · exact child2_generator_mem
    · exact child3_generator_mem
    · exact child4_generator_mem
    · exact child5_generator_mem
    · exact child6_generator_mem
    · exact child7_generator_mem
    · exact child8_generator_mem
    · exact child9_generator_mem
    · exact child10_generator_mem
    · exact child11_generator_mem
    · exact child12_generator_mem
    · exact child13_generator_mem
    · exact child14_generator_mem
    · exact child15_generator_mem
    · exact child16_generator_mem
    · exact child17_generator_mem
    · exact child18_generator_mem
    · exact child19_generator_mem
  lift_mem := by
    intro i
    fin_cases i
    · exact child0_lift_mem
    · exact child1_lift_mem
    · exact child2_lift_mem
    · exact child3_lift_mem
    · exact child4_lift_mem
    · exact child5_lift_mem
    · exact child6_lift_mem
    · exact child7_lift_mem
    · exact child8_lift_mem
    · exact child9_lift_mem
    · exact child10_lift_mem
    · exact child11_lift_mem
    · exact child12_lift_mem
    · exact child13_lift_mem
    · exact child14_lift_mem
    · exact child15_lift_mem
    · exact child16_lift_mem
    · exact child17_lift_mem
    · exact child18_lift_mem
    · exact child19_lift_mem
  child_card := by
    intro i
    fin_cases i
    · exact child0_card
    · exact child1_card
    · exact child2_card
    · exact child3_card
    · exact child4_card
    · exact child5_card
    · exact child6_card
    · exact child7_card
    · exact child8_card
    · exact child9_card
    · exact child10_card
    · exact child11_card
    · exact child12_card
    · exact child13_card
    · exact child14_card
    · exact child15_card
    · exact child16_card
    · exact child17_card
    · exact child18_card
    · exact child19_card

theorem source_isPGroup : IsPGroup 2 Source :=
  IsPGroup.of_card (n := 5) (by rw [source_card]; rfl)

/-- Every literal normal subgroup of the original faithful source appears.
There is no finite classification or producer-order assumption. -/
theorem complete (N : Subgroup Source) [N.Normal] :
    ∃ i, (states i).kernel=N := registry.complete source_isPGroup N

/-- Any semantic acceptance proved at all listed original normal states
holds for every actual normal subgroup of this source. -/
theorem all_normal_accepted (Accept : Subgroup Source → Prop)
    (haccept : ∀ i, Accept (states i).kernel)
    (N : Subgroup Source) [N.Normal] : Accept N :=
  registry.all_normal_accepted source_isPGroup Accept haccept N

end SymmetricSubgroupAsymptotics.BinaryNormal8T15
