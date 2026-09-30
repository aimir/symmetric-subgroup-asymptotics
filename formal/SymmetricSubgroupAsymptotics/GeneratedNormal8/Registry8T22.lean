import SymmetricSubgroupAsymptotics.GeneratedNormal8.States8T22

/-! All original normal subgroups of 8T22, by checked central-involution
closure in the complete literal quotient rows. Acceptance is separate. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryNormal8T22
local instance : Group Source := BinaryMenuCayley8T22.group

private def child0 (z : N0.state.Row) : Fin 68 :=
  ((if z.index.val < 16 then (if z.index.val < 8 then (if z.index.val < 4 then (if z.index.val < 2 then (if z.index.val < 1 then 0 else 1) else (if z.index.val < 3 then 0 else 0)) else (if z.index.val < 6 then (if z.index.val < 5 then 0 else 0) else (if z.index.val < 7 then 0 else 0))) else (if z.index.val < 12 then (if z.index.val < 10 then (if z.index.val < 9 then 0 else 0) else (if z.index.val < 11 then 0 else 0)) else (if z.index.val < 14 then (if z.index.val < 13 then 0 else 0) else (if z.index.val < 15 then 0 else 0)))) else (if z.index.val < 24 then (if z.index.val < 20 then (if z.index.val < 18 then (if z.index.val < 17 then 0 else 0) else (if z.index.val < 19 then 0 else 0)) else (if z.index.val < 22 then (if z.index.val < 21 then 0 else 0) else (if z.index.val < 23 then 0 else 0))) else (if z.index.val < 28 then (if z.index.val < 26 then (if z.index.val < 25 then 0 else 0) else (if z.index.val < 27 then 0 else 0)) else (if z.index.val < 30 then (if z.index.val < 29 then 0 else 0) else (if z.index.val < 31 then 0 else 0))))) : Fin 68)

private theorem child0_generator_mem (z : N0.state.Row)
    (hz : N0.state.CentralInvolution generators_full z) :
    ∀ j, N0.normalGenerators j ∈ (states (child0 z)).kernel := by
  have ht := N0.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(0 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · intro j
    exact Fin.elim0 j
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
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(24 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
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
  · change N0.cosets.representatives 1 ∈ N1.kernel
    have he : N0.cosets.representatives 1=
        (⟨N1.normalCertificate.rows 0⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N1.normalCertificate _
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
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(24 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
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
  · change Nat.card N1.kernel=Nat.card N0.kernel*2
    rw [N1.kernel_card,N0.kernel_card]
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
  · have hf : ¬N0.state.centralRowTests generators_full ⟨(24 : Fin 32)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
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

private def child1 (z : N1.state.Row) : Fin 68 :=
  ((if z.index.val < 8 then (if z.index.val < 4 then (if z.index.val < 2 then (if z.index.val < 1 then 0 else 6) else (if z.index.val < 3 then 11 else 4)) else (if z.index.val < 6 then (if z.index.val < 5 then 3 else 16) else (if z.index.val < 7 then 7 else 8))) else (if z.index.val < 12 then (if z.index.val < 10 then (if z.index.val < 9 then 10 else 9) else (if z.index.val < 11 then 2 else 13)) else (if z.index.val < 14 then (if z.index.val < 13 then 14 else 5) else (if z.index.val < 15 then 12 else 15)))) : Fin 68)

private theorem child1_generator_mem (z : N1.state.Row)
    (hz : N1.state.CentralInvolution generators_full z) :
    ∀ j, N1.normalGenerators j ∈ (states (child1 z)).kernel := by
  have ht := N1.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(0 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N1.normalGenerators j ∈ N6.kernel
    intro j
    have he : ∀ j : Fin 1, N1.normalGenerators j=
        (⟨N6.normalCertificate.rows ((0 : Fin 4))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N6.normalCertificate _
  · change ∀ j, N1.normalGenerators j ∈ N11.kernel
    intro j
    have he : ∀ j : Fin 1, N1.normalGenerators j=
        (⟨N11.normalCertificate.rows ((0 : Fin 4))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N11.normalCertificate _
  · change ∀ j, N1.normalGenerators j ∈ N4.kernel
    intro j
    have he : ∀ j : Fin 1, N1.normalGenerators j=
        (⟨N4.normalCertificate.rows ((0 : Fin 4))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N4.normalCertificate _
  · change ∀ j, N1.normalGenerators j ∈ N3.kernel
    intro j
    have he : ∀ j : Fin 1, N1.normalGenerators j=
        (⟨N3.normalCertificate.rows ((0 : Fin 4))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N3.normalCertificate _
  · change ∀ j, N1.normalGenerators j ∈ N16.kernel
    intro j
    have he : ∀ j : Fin 1, N1.normalGenerators j=
        (⟨N16.normalCertificate.rows ((0 : Fin 4))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N16.normalCertificate _
  · change ∀ j, N1.normalGenerators j ∈ N7.kernel
    intro j
    have he : ∀ j : Fin 1, N1.normalGenerators j=
        (⟨N7.normalCertificate.rows ((0 : Fin 4))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N7.normalCertificate _
  · change ∀ j, N1.normalGenerators j ∈ N8.kernel
    intro j
    have he : ∀ j : Fin 1, N1.normalGenerators j=
        (⟨N8.normalCertificate.rows ((0 : Fin 4))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N8.normalCertificate _
  · change ∀ j, N1.normalGenerators j ∈ N10.kernel
    intro j
    have he : ∀ j : Fin 1, N1.normalGenerators j=
        (⟨N10.normalCertificate.rows ((0 : Fin 4))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N10.normalCertificate _
  · change ∀ j, N1.normalGenerators j ∈ N9.kernel
    intro j
    have he : ∀ j : Fin 1, N1.normalGenerators j=
        (⟨N9.normalCertificate.rows ((0 : Fin 4))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N9.normalCertificate _
  · change ∀ j, N1.normalGenerators j ∈ N2.kernel
    intro j
    have he : ∀ j : Fin 1, N1.normalGenerators j=
        (⟨N2.normalCertificate.rows ((0 : Fin 4))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N2.normalCertificate _
  · change ∀ j, N1.normalGenerators j ∈ N13.kernel
    intro j
    have he : ∀ j : Fin 1, N1.normalGenerators j=
        (⟨N13.normalCertificate.rows ((0 : Fin 4))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N13.normalCertificate _
  · change ∀ j, N1.normalGenerators j ∈ N14.kernel
    intro j
    have he : ∀ j : Fin 1, N1.normalGenerators j=
        (⟨N14.normalCertificate.rows ((0 : Fin 4))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N14.normalCertificate _
  · change ∀ j, N1.normalGenerators j ∈ N5.kernel
    intro j
    have he : ∀ j : Fin 1, N1.normalGenerators j=
        (⟨N5.normalCertificate.rows ((0 : Fin 4))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N5.normalCertificate _
  · change ∀ j, N1.normalGenerators j ∈ N12.kernel
    intro j
    have he : ∀ j : Fin 1, N1.normalGenerators j=
        (⟨N12.normalCertificate.rows ((0 : Fin 4))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N12.normalCertificate _
  · change ∀ j, N1.normalGenerators j ∈ N15.kernel
    intro j
    have he : ∀ j : Fin 1, N1.normalGenerators j=
        (⟨N15.normalCertificate.rows ((0 : Fin 4))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N15.normalCertificate _

private theorem child1_lift_mem (z : N1.state.Row)
    (hz : N1.state.CentralInvolution generators_full z) :
    N1.cosets.representatives z.index ∈ (states (child1 z)).kernel := by
  have ht := N1.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(0 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N1.cosets.representatives 1 ∈ N6.kernel
    have he : N1.cosets.representatives 1=
        (⟨N6.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N6.normalCertificate _
  · change N1.cosets.representatives 2 ∈ N11.kernel
    have he : N1.cosets.representatives 2=
        (⟨N11.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N11.normalCertificate _
  · change N1.cosets.representatives 3 ∈ N4.kernel
    have he : N1.cosets.representatives 3=
        (⟨N4.normalCertificate.rows 2⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N4.normalCertificate _
  · change N1.cosets.representatives 4 ∈ N3.kernel
    have he : N1.cosets.representatives 4=
        (⟨N3.normalCertificate.rows 2⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N3.normalCertificate _
  · change N1.cosets.representatives 5 ∈ N16.kernel
    have he : N1.cosets.representatives 5=
        (⟨N16.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N16.normalCertificate _
  · change N1.cosets.representatives 6 ∈ N7.kernel
    have he : N1.cosets.representatives 6=
        (⟨N7.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N7.normalCertificate _
  · change N1.cosets.representatives 7 ∈ N8.kernel
    have he : N1.cosets.representatives 7=
        (⟨N8.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N8.normalCertificate _
  · change N1.cosets.representatives 8 ∈ N10.kernel
    have he : N1.cosets.representatives 8=
        (⟨N10.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N10.normalCertificate _
  · change N1.cosets.representatives 9 ∈ N9.kernel
    have he : N1.cosets.representatives 9=
        (⟨N9.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N9.normalCertificate _
  · change N1.cosets.representatives 10 ∈ N2.kernel
    have he : N1.cosets.representatives 10=
        (⟨N2.normalCertificate.rows 2⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N2.normalCertificate _
  · change N1.cosets.representatives 11 ∈ N13.kernel
    have he : N1.cosets.representatives 11=
        (⟨N13.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N13.normalCertificate _
  · change N1.cosets.representatives 12 ∈ N14.kernel
    have he : N1.cosets.representatives 12=
        (⟨N14.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N14.normalCertificate _
  · change N1.cosets.representatives 13 ∈ N5.kernel
    have he : N1.cosets.representatives 13=
        (⟨N5.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N5.normalCertificate _
  · change N1.cosets.representatives 14 ∈ N12.kernel
    have he : N1.cosets.representatives 14=
        (⟨N12.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N12.normalCertificate _
  · change N1.cosets.representatives 15 ∈ N15.kernel
    have he : N1.cosets.representatives 15=
        (⟨N15.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N15.normalCertificate _

private theorem child1_card (z : N1.state.Row)
    (hz : N1.state.CentralInvolution generators_full z) :
    Nat.card (states (child1 z)).kernel=Nat.card N1.kernel*2 := by
  have ht := N1.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N1.state.centralRowTests generators_full ⟨(0 : Fin 16)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N6.kernel=Nat.card N1.kernel*2
    rw [N6.kernel_card,N1.kernel_card]
  · change Nat.card N11.kernel=Nat.card N1.kernel*2
    rw [N11.kernel_card,N1.kernel_card]
  · change Nat.card N4.kernel=Nat.card N1.kernel*2
    rw [N4.kernel_card,N1.kernel_card]
  · change Nat.card N3.kernel=Nat.card N1.kernel*2
    rw [N3.kernel_card,N1.kernel_card]
  · change Nat.card N16.kernel=Nat.card N1.kernel*2
    rw [N16.kernel_card,N1.kernel_card]
  · change Nat.card N7.kernel=Nat.card N1.kernel*2
    rw [N7.kernel_card,N1.kernel_card]
  · change Nat.card N8.kernel=Nat.card N1.kernel*2
    rw [N8.kernel_card,N1.kernel_card]
  · change Nat.card N10.kernel=Nat.card N1.kernel*2
    rw [N10.kernel_card,N1.kernel_card]
  · change Nat.card N9.kernel=Nat.card N1.kernel*2
    rw [N9.kernel_card,N1.kernel_card]
  · change Nat.card N2.kernel=Nat.card N1.kernel*2
    rw [N2.kernel_card,N1.kernel_card]
  · change Nat.card N13.kernel=Nat.card N1.kernel*2
    rw [N13.kernel_card,N1.kernel_card]
  · change Nat.card N14.kernel=Nat.card N1.kernel*2
    rw [N14.kernel_card,N1.kernel_card]
  · change Nat.card N5.kernel=Nat.card N1.kernel*2
    rw [N5.kernel_card,N1.kernel_card]
  · change Nat.card N12.kernel=Nat.card N1.kernel*2
    rw [N12.kernel_card,N1.kernel_card]
  · change Nat.card N15.kernel=Nat.card N1.kernel*2
    rw [N15.kernel_card,N1.kernel_card]

private def child2 (z : N2.state.Row) : Fin 68 :=
  ((if z.index.val < 4 then (if z.index.val < 2 then (if z.index.val < 1 then 0 else 18) else (if z.index.val < 3 then 21 else 17)) else (if z.index.val < 6 then (if z.index.val < 5 then 23 else 19) else (if z.index.val < 7 then 20 else 22))) : Fin 68)

private theorem child2_generator_mem (z : N2.state.Row)
    (hz : N2.state.CentralInvolution generators_full z) :
    ∀ j, N2.normalGenerators j ∈ (states (child2 z)).kernel := by
  have ht := N2.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N2.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N2.normalGenerators j ∈ N18.kernel
    intro j
    have he : ∀ j : Fin 2, N2.normalGenerators j=
        (⟨N18.normalCertificate.rows (((if j.val < 1 then 6 else 1) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N18.normalCertificate _
  · change ∀ j, N2.normalGenerators j ∈ N21.kernel
    intro j
    have he : ∀ j : Fin 2, N2.normalGenerators j=
        (⟨N21.normalCertificate.rows (((if j.val < 1 then 6 else 1) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N21.normalCertificate _
  · change ∀ j, N2.normalGenerators j ∈ N17.kernel
    intro j
    have he : ∀ j : Fin 2, N2.normalGenerators j=
        (⟨N17.normalCertificate.rows (((if j.val < 1 then 4 else 3) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N17.normalCertificate _
  · change ∀ j, N2.normalGenerators j ∈ N23.kernel
    intro j
    have he : ∀ j : Fin 2, N2.normalGenerators j=
        (⟨N23.normalCertificate.rows (((if j.val < 1 then 6 else 1) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N23.normalCertificate _
  · change ∀ j, N2.normalGenerators j ∈ N19.kernel
    intro j
    have he : ∀ j : Fin 2, N2.normalGenerators j=
        (⟨N19.normalCertificate.rows (((if j.val < 1 then 6 else 1) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N19.normalCertificate _
  · change ∀ j, N2.normalGenerators j ∈ N20.kernel
    intro j
    have he : ∀ j : Fin 2, N2.normalGenerators j=
        (⟨N20.normalCertificate.rows (((if j.val < 1 then 6 else 1) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N20.normalCertificate _
  · change ∀ j, N2.normalGenerators j ∈ N22.kernel
    intro j
    have he : ∀ j : Fin 2, N2.normalGenerators j=
        (⟨N22.normalCertificate.rows (((if j.val < 1 then 6 else 1) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N22.normalCertificate _

private theorem child2_lift_mem (z : N2.state.Row)
    (hz : N2.state.CentralInvolution generators_full z) :
    N2.cosets.representatives z.index ∈ (states (child2 z)).kernel := by
  have ht := N2.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N2.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N2.cosets.representatives 1 ∈ N18.kernel
    have he : N2.cosets.representatives 1=
        (⟨N18.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N18.normalCertificate _
  · change N2.cosets.representatives 2 ∈ N21.kernel
    have he : N2.cosets.representatives 2=
        (⟨N21.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N21.normalCertificate _
  · change N2.cosets.representatives 3 ∈ N17.kernel
    have he : N2.cosets.representatives 3=
        (⟨N17.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N17.normalCertificate _
  · change N2.cosets.representatives 4 ∈ N23.kernel
    have he : N2.cosets.representatives 4=
        (⟨N23.normalCertificate.rows 2⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N23.normalCertificate _
  · change N2.cosets.representatives 5 ∈ N19.kernel
    have he : N2.cosets.representatives 5=
        (⟨N19.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N19.normalCertificate _
  · change N2.cosets.representatives 6 ∈ N20.kernel
    have he : N2.cosets.representatives 6=
        (⟨N20.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N20.normalCertificate _
  · change N2.cosets.representatives 7 ∈ N22.kernel
    have he : N2.cosets.representatives 7=
        (⟨N22.normalCertificate.rows 2⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N22.normalCertificate _

private theorem child2_card (z : N2.state.Row)
    (hz : N2.state.CentralInvolution generators_full z) :
    Nat.card (states (child2 z)).kernel=Nat.card N2.kernel*2 := by
  have ht := N2.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N2.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N18.kernel=Nat.card N2.kernel*2
    rw [N18.kernel_card,N2.kernel_card]
  · change Nat.card N21.kernel=Nat.card N2.kernel*2
    rw [N21.kernel_card,N2.kernel_card]
  · change Nat.card N17.kernel=Nat.card N2.kernel*2
    rw [N17.kernel_card,N2.kernel_card]
  · change Nat.card N23.kernel=Nat.card N2.kernel*2
    rw [N23.kernel_card,N2.kernel_card]
  · change Nat.card N19.kernel=Nat.card N2.kernel*2
    rw [N19.kernel_card,N2.kernel_card]
  · change Nat.card N20.kernel=Nat.card N2.kernel*2
    rw [N20.kernel_card,N2.kernel_card]
  · change Nat.card N22.kernel=Nat.card N2.kernel*2
    rw [N22.kernel_card,N2.kernel_card]

private def child3 (z : N3.state.Row) : Fin 68 :=
  ((if z.index.val < 4 then (if z.index.val < 2 then (if z.index.val < 1 then 0 else 25) else (if z.index.val < 3 then 26 else 17)) else (if z.index.val < 6 then (if z.index.val < 5 then 29 else 24) else (if z.index.val < 7 then 27 else 28))) : Fin 68)

private theorem child3_generator_mem (z : N3.state.Row)
    (hz : N3.state.CentralInvolution generators_full z) :
    ∀ j, N3.normalGenerators j ∈ (states (child3 z)).kernel := by
  have ht := N3.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N3.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N3.normalGenerators j ∈ N25.kernel
    intro j
    have he : ∀ j : Fin 2, N3.normalGenerators j=
        (⟨N25.normalCertificate.rows (((if j.val < 1 then 6 else 1) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N25.normalCertificate _
  · change ∀ j, N3.normalGenerators j ∈ N26.kernel
    intro j
    have he : ∀ j : Fin 2, N3.normalGenerators j=
        (⟨N26.normalCertificate.rows (((if j.val < 1 then 6 else 1) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N26.normalCertificate _
  · change ∀ j, N3.normalGenerators j ∈ N17.kernel
    intro j
    have he : ∀ j : Fin 2, N3.normalGenerators j=
        (⟨N17.normalCertificate.rows (((if j.val < 1 then 5 else 2) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N17.normalCertificate _
  · change ∀ j, N3.normalGenerators j ∈ N29.kernel
    intro j
    have he : ∀ j : Fin 2, N3.normalGenerators j=
        (⟨N29.normalCertificate.rows (((if j.val < 1 then 6 else 1) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N29.normalCertificate _
  · change ∀ j, N3.normalGenerators j ∈ N24.kernel
    intro j
    have he : ∀ j : Fin 2, N3.normalGenerators j=
        (⟨N24.normalCertificate.rows (((if j.val < 1 then 6 else 1) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N24.normalCertificate _
  · change ∀ j, N3.normalGenerators j ∈ N27.kernel
    intro j
    have he : ∀ j : Fin 2, N3.normalGenerators j=
        (⟨N27.normalCertificate.rows (((if j.val < 1 then 6 else 1) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N27.normalCertificate _
  · change ∀ j, N3.normalGenerators j ∈ N28.kernel
    intro j
    have he : ∀ j : Fin 2, N3.normalGenerators j=
        (⟨N28.normalCertificate.rows (((if j.val < 1 then 6 else 1) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N28.normalCertificate _

private theorem child3_lift_mem (z : N3.state.Row)
    (hz : N3.state.CentralInvolution generators_full z) :
    N3.cosets.representatives z.index ∈ (states (child3 z)).kernel := by
  have ht := N3.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N3.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N3.cosets.representatives 1 ∈ N25.kernel
    have he : N3.cosets.representatives 1=
        (⟨N25.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N25.normalCertificate _
  · change N3.cosets.representatives 2 ∈ N26.kernel
    have he : N3.cosets.representatives 2=
        (⟨N26.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N26.normalCertificate _
  · change N3.cosets.representatives 3 ∈ N17.kernel
    have he : N3.cosets.representatives 3=
        (⟨N17.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N17.normalCertificate _
  · change N3.cosets.representatives 4 ∈ N29.kernel
    have he : N3.cosets.representatives 4=
        (⟨N29.normalCertificate.rows 2⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N29.normalCertificate _
  · change N3.cosets.representatives 5 ∈ N24.kernel
    have he : N3.cosets.representatives 5=
        (⟨N24.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N24.normalCertificate _
  · change N3.cosets.representatives 6 ∈ N27.kernel
    have he : N3.cosets.representatives 6=
        (⟨N27.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N27.normalCertificate _
  · change N3.cosets.representatives 7 ∈ N28.kernel
    have he : N3.cosets.representatives 7=
        (⟨N28.normalCertificate.rows 2⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N28.normalCertificate _

private theorem child3_card (z : N3.state.Row)
    (hz : N3.state.CentralInvolution generators_full z) :
    Nat.card (states (child3 z)).kernel=Nat.card N3.kernel*2 := by
  have ht := N3.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N3.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N25.kernel=Nat.card N3.kernel*2
    rw [N25.kernel_card,N3.kernel_card]
  · change Nat.card N26.kernel=Nat.card N3.kernel*2
    rw [N26.kernel_card,N3.kernel_card]
  · change Nat.card N17.kernel=Nat.card N3.kernel*2
    rw [N17.kernel_card,N3.kernel_card]
  · change Nat.card N29.kernel=Nat.card N3.kernel*2
    rw [N29.kernel_card,N3.kernel_card]
  · change Nat.card N24.kernel=Nat.card N3.kernel*2
    rw [N24.kernel_card,N3.kernel_card]
  · change Nat.card N27.kernel=Nat.card N3.kernel*2
    rw [N27.kernel_card,N3.kernel_card]
  · change Nat.card N28.kernel=Nat.card N3.kernel*2
    rw [N28.kernel_card,N3.kernel_card]

private def child4 (z : N4.state.Row) : Fin 68 :=
  ((if z.index.val < 4 then (if z.index.val < 2 then (if z.index.val < 1 then 0 else 31) else (if z.index.val < 3 then 33 else 17)) else (if z.index.val < 6 then (if z.index.val < 5 then 34 else 30) else (if z.index.val < 7 then 32 else 35))) : Fin 68)

private theorem child4_generator_mem (z : N4.state.Row)
    (hz : N4.state.CentralInvolution generators_full z) :
    ∀ j, N4.normalGenerators j ∈ (states (child4 z)).kernel := by
  have ht := N4.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N4.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N4.normalGenerators j ∈ N31.kernel
    intro j
    have he : ∀ j : Fin 2, N4.normalGenerators j=
        (⟨N31.normalCertificate.rows (((if j.val < 1 then 6 else 1) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N31.normalCertificate _
  · change ∀ j, N4.normalGenerators j ∈ N33.kernel
    intro j
    have he : ∀ j : Fin 2, N4.normalGenerators j=
        (⟨N33.normalCertificate.rows (((if j.val < 1 then 6 else 1) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N33.normalCertificate _
  · change ∀ j, N4.normalGenerators j ∈ N17.kernel
    intro j
    have he : ∀ j : Fin 2, N4.normalGenerators j=
        (⟨N17.normalCertificate.rows (((if j.val < 1 then 6 else 1) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N17.normalCertificate _
  · change ∀ j, N4.normalGenerators j ∈ N34.kernel
    intro j
    have he : ∀ j : Fin 2, N4.normalGenerators j=
        (⟨N34.normalCertificate.rows (((if j.val < 1 then 6 else 1) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N34.normalCertificate _
  · change ∀ j, N4.normalGenerators j ∈ N30.kernel
    intro j
    have he : ∀ j : Fin 2, N4.normalGenerators j=
        (⟨N30.normalCertificate.rows (((if j.val < 1 then 6 else 1) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N30.normalCertificate _
  · change ∀ j, N4.normalGenerators j ∈ N32.kernel
    intro j
    have he : ∀ j : Fin 2, N4.normalGenerators j=
        (⟨N32.normalCertificate.rows (((if j.val < 1 then 6 else 1) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N32.normalCertificate _
  · change ∀ j, N4.normalGenerators j ∈ N35.kernel
    intro j
    have he : ∀ j : Fin 2, N4.normalGenerators j=
        (⟨N35.normalCertificate.rows (((if j.val < 1 then 6 else 1) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N35.normalCertificate _

private theorem child4_lift_mem (z : N4.state.Row)
    (hz : N4.state.CentralInvolution generators_full z) :
    N4.cosets.representatives z.index ∈ (states (child4 z)).kernel := by
  have ht := N4.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N4.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N4.cosets.representatives 1 ∈ N31.kernel
    have he : N4.cosets.representatives 1=
        (⟨N31.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N31.normalCertificate _
  · change N4.cosets.representatives 2 ∈ N33.kernel
    have he : N4.cosets.representatives 2=
        (⟨N33.normalCertificate.rows 2⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N33.normalCertificate _
  · change N4.cosets.representatives 3 ∈ N17.kernel
    have he : N4.cosets.representatives 3=
        (⟨N17.normalCertificate.rows 5⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N17.normalCertificate _
  · change N4.cosets.representatives 4 ∈ N34.kernel
    have he : N4.cosets.representatives 4=
        (⟨N34.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N34.normalCertificate _
  · change N4.cosets.representatives 5 ∈ N30.kernel
    have he : N4.cosets.representatives 5=
        (⟨N30.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N30.normalCertificate _
  · change N4.cosets.representatives 6 ∈ N32.kernel
    have he : N4.cosets.representatives 6=
        (⟨N32.normalCertificate.rows 2⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N32.normalCertificate _
  · change N4.cosets.representatives 7 ∈ N35.kernel
    have he : N4.cosets.representatives 7=
        (⟨N35.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N35.normalCertificate _

private theorem child4_card (z : N4.state.Row)
    (hz : N4.state.CentralInvolution generators_full z) :
    Nat.card (states (child4 z)).kernel=Nat.card N4.kernel*2 := by
  have ht := N4.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N4.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N31.kernel=Nat.card N4.kernel*2
    rw [N31.kernel_card,N4.kernel_card]
  · change Nat.card N33.kernel=Nat.card N4.kernel*2
    rw [N33.kernel_card,N4.kernel_card]
  · change Nat.card N17.kernel=Nat.card N4.kernel*2
    rw [N17.kernel_card,N4.kernel_card]
  · change Nat.card N34.kernel=Nat.card N4.kernel*2
    rw [N34.kernel_card,N4.kernel_card]
  · change Nat.card N30.kernel=Nat.card N4.kernel*2
    rw [N30.kernel_card,N4.kernel_card]
  · change Nat.card N32.kernel=Nat.card N4.kernel*2
    rw [N32.kernel_card,N4.kernel_card]
  · change Nat.card N35.kernel=Nat.card N4.kernel*2
    rw [N35.kernel_card,N4.kernel_card]

private def child5 (z : N5.state.Row) : Fin 68 :=
  ((if z.index.val < 4 then (if z.index.val < 2 then (if z.index.val < 1 then 0 else 18) else (if z.index.val < 3 then 38 else 30)) else (if z.index.val < 6 then (if z.index.val < 5 then 24 else 39) else (if z.index.val < 7 then 37 else 36))) : Fin 68)

private theorem child5_generator_mem (z : N5.state.Row)
    (hz : N5.state.CentralInvolution generators_full z) :
    ∀ j, N5.normalGenerators j ∈ (states (child5 z)).kernel := by
  have ht := N5.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N5.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N5.normalGenerators j ∈ N18.kernel
    intro j
    have he : ∀ j : Fin 2, N5.normalGenerators j=
        (⟨N18.normalCertificate.rows (((if j.val < 1 then 5 else 2) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N18.normalCertificate _
  · change ∀ j, N5.normalGenerators j ∈ N38.kernel
    intro j
    have he : ∀ j : Fin 2, N5.normalGenerators j=
        (⟨N38.normalCertificate.rows (((if j.val < 1 then 2 else 1) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N38.normalCertificate _
  · change ∀ j, N5.normalGenerators j ∈ N30.kernel
    intro j
    have he : ∀ j : Fin 2, N5.normalGenerators j=
        (⟨N30.normalCertificate.rows (((if j.val < 1 then 5 else 2) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N30.normalCertificate _
  · change ∀ j, N5.normalGenerators j ∈ N24.kernel
    intro j
    have he : ∀ j : Fin 2, N5.normalGenerators j=
        (⟨N24.normalCertificate.rows (((if j.val < 1 then 5 else 2) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N24.normalCertificate _
  · change ∀ j, N5.normalGenerators j ∈ N39.kernel
    intro j
    have he : ∀ j : Fin 2, N5.normalGenerators j=
        (⟨N39.normalCertificate.rows (((if j.val < 1 then 2 else 1) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N39.normalCertificate _
  · change ∀ j, N5.normalGenerators j ∈ N37.kernel
    intro j
    have he : ∀ j : Fin 2, N5.normalGenerators j=
        (⟨N37.normalCertificate.rows (((if j.val < 1 then 2 else 1) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N37.normalCertificate _
  · change ∀ j, N5.normalGenerators j ∈ N36.kernel
    intro j
    have he : ∀ j : Fin 2, N5.normalGenerators j=
        (⟨N36.normalCertificate.rows (((if j.val < 1 then 2 else 1) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N36.normalCertificate _

private theorem child5_lift_mem (z : N5.state.Row)
    (hz : N5.state.CentralInvolution generators_full z) :
    N5.cosets.representatives z.index ∈ (states (child5 z)).kernel := by
  have ht := N5.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N5.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N5.cosets.representatives 1 ∈ N18.kernel
    have he : N5.cosets.representatives 1=
        (⟨N18.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N18.normalCertificate _
  · change N5.cosets.representatives 2 ∈ N38.kernel
    have he : N5.cosets.representatives 2=
        (⟨N38.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N38.normalCertificate _
  · change N5.cosets.representatives 3 ∈ N30.kernel
    have he : N5.cosets.representatives 3=
        (⟨N30.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N30.normalCertificate _
  · change N5.cosets.representatives 4 ∈ N24.kernel
    have he : N5.cosets.representatives 4=
        (⟨N24.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N24.normalCertificate _
  · change N5.cosets.representatives 5 ∈ N39.kernel
    have he : N5.cosets.representatives 5=
        (⟨N39.normalCertificate.rows 5⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N39.normalCertificate _
  · change N5.cosets.representatives 6 ∈ N37.kernel
    have he : N5.cosets.representatives 6=
        (⟨N37.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N37.normalCertificate _
  · change N5.cosets.representatives 7 ∈ N36.kernel
    have he : N5.cosets.representatives 7=
        (⟨N36.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N36.normalCertificate _

private theorem child5_card (z : N5.state.Row)
    (hz : N5.state.CentralInvolution generators_full z) :
    Nat.card (states (child5 z)).kernel=Nat.card N5.kernel*2 := by
  have ht := N5.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N5.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N18.kernel=Nat.card N5.kernel*2
    rw [N18.kernel_card,N5.kernel_card]
  · change Nat.card N38.kernel=Nat.card N5.kernel*2
    rw [N38.kernel_card,N5.kernel_card]
  · change Nat.card N30.kernel=Nat.card N5.kernel*2
    rw [N30.kernel_card,N5.kernel_card]
  · change Nat.card N24.kernel=Nat.card N5.kernel*2
    rw [N24.kernel_card,N5.kernel_card]
  · change Nat.card N39.kernel=Nat.card N5.kernel*2
    rw [N39.kernel_card,N5.kernel_card]
  · change Nat.card N37.kernel=Nat.card N5.kernel*2
    rw [N37.kernel_card,N5.kernel_card]
  · change Nat.card N36.kernel=Nat.card N5.kernel*2
    rw [N36.kernel_card,N5.kernel_card]

private def child6 (z : N6.state.Row) : Fin 68 :=
  ((if z.index.val < 4 then (if z.index.val < 2 then (if z.index.val < 1 then 0 else 42) else (if z.index.val < 3 then 31 else 25)) else (if z.index.val < 6 then (if z.index.val < 5 then 41 else 40) else (if z.index.val < 7 then 18 else 43))) : Fin 68)

private theorem child6_generator_mem (z : N6.state.Row)
    (hz : N6.state.CentralInvolution generators_full z) :
    ∀ j, N6.normalGenerators j ∈ (states (child6 z)).kernel := by
  have ht := N6.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N6.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N6.normalGenerators j ∈ N42.kernel
    intro j
    have he : ∀ j : Fin 2, N6.normalGenerators j=
        (⟨N42.normalCertificate.rows (((if j.val < 1 then 2 else 1) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N42.normalCertificate _
  · change ∀ j, N6.normalGenerators j ∈ N31.kernel
    intro j
    have he : ∀ j : Fin 2, N6.normalGenerators j=
        (⟨N31.normalCertificate.rows (((if j.val < 1 then 4 else 3) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N31.normalCertificate _
  · change ∀ j, N6.normalGenerators j ∈ N25.kernel
    intro j
    have he : ∀ j : Fin 2, N6.normalGenerators j=
        (⟨N25.normalCertificate.rows (((if j.val < 1 then 4 else 3) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N25.normalCertificate _
  · change ∀ j, N6.normalGenerators j ∈ N41.kernel
    intro j
    have he : ∀ j : Fin 2, N6.normalGenerators j=
        (⟨N41.normalCertificate.rows (((if j.val < 1 then 2 else 1) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N41.normalCertificate _
  · change ∀ j, N6.normalGenerators j ∈ N40.kernel
    intro j
    have he : ∀ j : Fin 2, N6.normalGenerators j=
        (⟨N40.normalCertificate.rows (((if j.val < 1 then 2 else 1) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N40.normalCertificate _
  · change ∀ j, N6.normalGenerators j ∈ N18.kernel
    intro j
    have he : ∀ j : Fin 2, N6.normalGenerators j=
        (⟨N18.normalCertificate.rows (((if j.val < 1 then 4 else 3) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N18.normalCertificate _
  · change ∀ j, N6.normalGenerators j ∈ N43.kernel
    intro j
    have he : ∀ j : Fin 2, N6.normalGenerators j=
        (⟨N43.normalCertificate.rows (((if j.val < 1 then 2 else 1) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N43.normalCertificate _

private theorem child6_lift_mem (z : N6.state.Row)
    (hz : N6.state.CentralInvolution generators_full z) :
    N6.cosets.representatives z.index ∈ (states (child6 z)).kernel := by
  have ht := N6.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N6.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N6.cosets.representatives 1 ∈ N42.kernel
    have he : N6.cosets.representatives 1=
        (⟨N42.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N42.normalCertificate _
  · change N6.cosets.representatives 2 ∈ N31.kernel
    have he : N6.cosets.representatives 2=
        (⟨N31.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N31.normalCertificate _
  · change N6.cosets.representatives 3 ∈ N25.kernel
    have he : N6.cosets.representatives 3=
        (⟨N25.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N25.normalCertificate _
  · change N6.cosets.representatives 4 ∈ N41.kernel
    have he : N6.cosets.representatives 4=
        (⟨N41.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N41.normalCertificate _
  · change N6.cosets.representatives 5 ∈ N40.kernel
    have he : N6.cosets.representatives 5=
        (⟨N40.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N40.normalCertificate _
  · change N6.cosets.representatives 6 ∈ N18.kernel
    have he : N6.cosets.representatives 6=
        (⟨N18.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N18.normalCertificate _
  · change N6.cosets.representatives 7 ∈ N43.kernel
    have he : N6.cosets.representatives 7=
        (⟨N43.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N43.normalCertificate _

private theorem child6_card (z : N6.state.Row)
    (hz : N6.state.CentralInvolution generators_full z) :
    Nat.card (states (child6 z)).kernel=Nat.card N6.kernel*2 := by
  have ht := N6.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N6.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N42.kernel=Nat.card N6.kernel*2
    rw [N42.kernel_card,N6.kernel_card]
  · change Nat.card N31.kernel=Nat.card N6.kernel*2
    rw [N31.kernel_card,N6.kernel_card]
  · change Nat.card N25.kernel=Nat.card N6.kernel*2
    rw [N25.kernel_card,N6.kernel_card]
  · change Nat.card N41.kernel=Nat.card N6.kernel*2
    rw [N41.kernel_card,N6.kernel_card]
  · change Nat.card N40.kernel=Nat.card N6.kernel*2
    rw [N40.kernel_card,N6.kernel_card]
  · change Nat.card N18.kernel=Nat.card N6.kernel*2
    rw [N18.kernel_card,N6.kernel_card]
  · change Nat.card N43.kernel=Nat.card N6.kernel*2
    rw [N43.kernel_card,N6.kernel_card]

private def child7 (z : N7.state.Row) : Fin 68 :=
  ((if z.index.val < 4 then (if z.index.val < 2 then (if z.index.val < 1 then 0 else 31) else (if z.index.val < 3 then 46 else 24)) else (if z.index.val < 6 then (if z.index.val < 5 then 45 else 19) else (if z.index.val < 7 then 44 else 47))) : Fin 68)

private theorem child7_generator_mem (z : N7.state.Row)
    (hz : N7.state.CentralInvolution generators_full z) :
    ∀ j, N7.normalGenerators j ∈ (states (child7 z)).kernel := by
  have ht := N7.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N7.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N7.normalGenerators j ∈ N31.kernel
    intro j
    have he : ∀ j : Fin 1, N7.normalGenerators j=
        (⟨N31.normalCertificate.rows ((5 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N31.normalCertificate _
  · change ∀ j, N7.normalGenerators j ∈ N46.kernel
    intro j
    have he : ∀ j : Fin 1, N7.normalGenerators j=
        (⟨N46.normalCertificate.rows ((2 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N46.normalCertificate _
  · change ∀ j, N7.normalGenerators j ∈ N24.kernel
    intro j
    have he : ∀ j : Fin 1, N7.normalGenerators j=
        (⟨N24.normalCertificate.rows ((4 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N24.normalCertificate _
  · change ∀ j, N7.normalGenerators j ∈ N45.kernel
    intro j
    have he : ∀ j : Fin 1, N7.normalGenerators j=
        (⟨N45.normalCertificate.rows ((2 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N45.normalCertificate _
  · change ∀ j, N7.normalGenerators j ∈ N19.kernel
    intro j
    have he : ∀ j : Fin 1, N7.normalGenerators j=
        (⟨N19.normalCertificate.rows ((4 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N19.normalCertificate _
  · change ∀ j, N7.normalGenerators j ∈ N44.kernel
    intro j
    have he : ∀ j : Fin 1, N7.normalGenerators j=
        (⟨N44.normalCertificate.rows ((2 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N44.normalCertificate _
  · change ∀ j, N7.normalGenerators j ∈ N47.kernel
    intro j
    have he : ∀ j : Fin 1, N7.normalGenerators j=
        (⟨N47.normalCertificate.rows ((2 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N47.normalCertificate _

private theorem child7_lift_mem (z : N7.state.Row)
    (hz : N7.state.CentralInvolution generators_full z) :
    N7.cosets.representatives z.index ∈ (states (child7 z)).kernel := by
  have ht := N7.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N7.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N7.cosets.representatives 1 ∈ N31.kernel
    have he : N7.cosets.representatives 1=
        (⟨N31.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N31.normalCertificate _
  · change N7.cosets.representatives 2 ∈ N46.kernel
    have he : N7.cosets.representatives 2=
        (⟨N46.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N46.normalCertificate _
  · change N7.cosets.representatives 3 ∈ N24.kernel
    have he : N7.cosets.representatives 3=
        (⟨N24.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N24.normalCertificate _
  · change N7.cosets.representatives 4 ∈ N45.kernel
    have he : N7.cosets.representatives 4=
        (⟨N45.normalCertificate.rows 5⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N45.normalCertificate _
  · change N7.cosets.representatives 5 ∈ N19.kernel
    have he : N7.cosets.representatives 5=
        (⟨N19.normalCertificate.rows 2⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N19.normalCertificate _
  · change N7.cosets.representatives 6 ∈ N44.kernel
    have he : N7.cosets.representatives 6=
        (⟨N44.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N44.normalCertificate _
  · change N7.cosets.representatives 7 ∈ N47.kernel
    have he : N7.cosets.representatives 7=
        (⟨N47.normalCertificate.rows 5⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N47.normalCertificate _

private theorem child7_card (z : N7.state.Row)
    (hz : N7.state.CentralInvolution generators_full z) :
    Nat.card (states (child7 z)).kernel=Nat.card N7.kernel*2 := by
  have ht := N7.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N7.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N31.kernel=Nat.card N7.kernel*2
    rw [N31.kernel_card,N7.kernel_card]
  · change Nat.card N46.kernel=Nat.card N7.kernel*2
    rw [N46.kernel_card,N7.kernel_card]
  · change Nat.card N24.kernel=Nat.card N7.kernel*2
    rw [N24.kernel_card,N7.kernel_card]
  · change Nat.card N45.kernel=Nat.card N7.kernel*2
    rw [N45.kernel_card,N7.kernel_card]
  · change Nat.card N19.kernel=Nat.card N7.kernel*2
    rw [N19.kernel_card,N7.kernel_card]
  · change Nat.card N44.kernel=Nat.card N7.kernel*2
    rw [N44.kernel_card,N7.kernel_card]
  · change Nat.card N47.kernel=Nat.card N7.kernel*2
    rw [N47.kernel_card,N7.kernel_card]

private def child8 (z : N8.state.Row) : Fin 68 :=
  ((if z.index.val < 4 then (if z.index.val < 2 then (if z.index.val < 1 then 0 else 25) else (if z.index.val < 3 then 50 else 30)) else (if z.index.val < 6 then (if z.index.val < 5 then 48 else 19) else (if z.index.val < 7 then 49 else 51))) : Fin 68)

private theorem child8_generator_mem (z : N8.state.Row)
    (hz : N8.state.CentralInvolution generators_full z) :
    ∀ j, N8.normalGenerators j ∈ (states (child8 z)).kernel := by
  have ht := N8.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N8.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N8.normalGenerators j ∈ N25.kernel
    intro j
    have he : ∀ j : Fin 1, N8.normalGenerators j=
        (⟨N25.normalCertificate.rows ((5 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N25.normalCertificate _
  · change ∀ j, N8.normalGenerators j ∈ N50.kernel
    intro j
    have he : ∀ j : Fin 1, N8.normalGenerators j=
        (⟨N50.normalCertificate.rows ((2 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N50.normalCertificate _
  · change ∀ j, N8.normalGenerators j ∈ N30.kernel
    intro j
    have he : ∀ j : Fin 1, N8.normalGenerators j=
        (⟨N30.normalCertificate.rows ((4 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N30.normalCertificate _
  · change ∀ j, N8.normalGenerators j ∈ N48.kernel
    intro j
    have he : ∀ j : Fin 1, N8.normalGenerators j=
        (⟨N48.normalCertificate.rows ((2 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N48.normalCertificate _
  · change ∀ j, N8.normalGenerators j ∈ N19.kernel
    intro j
    have he : ∀ j : Fin 1, N8.normalGenerators j=
        (⟨N19.normalCertificate.rows ((5 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N19.normalCertificate _
  · change ∀ j, N8.normalGenerators j ∈ N49.kernel
    intro j
    have he : ∀ j : Fin 1, N8.normalGenerators j=
        (⟨N49.normalCertificate.rows ((2 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N49.normalCertificate _
  · change ∀ j, N8.normalGenerators j ∈ N51.kernel
    intro j
    have he : ∀ j : Fin 1, N8.normalGenerators j=
        (⟨N51.normalCertificate.rows ((2 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N51.normalCertificate _

private theorem child8_lift_mem (z : N8.state.Row)
    (hz : N8.state.CentralInvolution generators_full z) :
    N8.cosets.representatives z.index ∈ (states (child8 z)).kernel := by
  have ht := N8.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N8.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N8.cosets.representatives 1 ∈ N25.kernel
    have he : N8.cosets.representatives 1=
        (⟨N25.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N25.normalCertificate _
  · change N8.cosets.representatives 2 ∈ N50.kernel
    have he : N8.cosets.representatives 2=
        (⟨N50.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N50.normalCertificate _
  · change N8.cosets.representatives 3 ∈ N30.kernel
    have he : N8.cosets.representatives 3=
        (⟨N30.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N30.normalCertificate _
  · change N8.cosets.representatives 4 ∈ N48.kernel
    have he : N8.cosets.representatives 4=
        (⟨N48.normalCertificate.rows 5⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N48.normalCertificate _
  · change N8.cosets.representatives 5 ∈ N19.kernel
    have he : N8.cosets.representatives 5=
        (⟨N19.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N19.normalCertificate _
  · change N8.cosets.representatives 6 ∈ N49.kernel
    have he : N8.cosets.representatives 6=
        (⟨N49.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N49.normalCertificate _
  · change N8.cosets.representatives 7 ∈ N51.kernel
    have he : N8.cosets.representatives 7=
        (⟨N51.normalCertificate.rows 5⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N51.normalCertificate _

private theorem child8_card (z : N8.state.Row)
    (hz : N8.state.CentralInvolution generators_full z) :
    Nat.card (states (child8 z)).kernel=Nat.card N8.kernel*2 := by
  have ht := N8.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N8.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N25.kernel=Nat.card N8.kernel*2
    rw [N25.kernel_card,N8.kernel_card]
  · change Nat.card N50.kernel=Nat.card N8.kernel*2
    rw [N50.kernel_card,N8.kernel_card]
  · change Nat.card N30.kernel=Nat.card N8.kernel*2
    rw [N30.kernel_card,N8.kernel_card]
  · change Nat.card N48.kernel=Nat.card N8.kernel*2
    rw [N48.kernel_card,N8.kernel_card]
  · change Nat.card N19.kernel=Nat.card N8.kernel*2
    rw [N19.kernel_card,N8.kernel_card]
  · change Nat.card N49.kernel=Nat.card N8.kernel*2
    rw [N49.kernel_card,N8.kernel_card]
  · change Nat.card N51.kernel=Nat.card N8.kernel*2
    rw [N51.kernel_card,N8.kernel_card]

private def child9 (z : N9.state.Row) : Fin 68 :=
  ((if z.index.val < 4 then (if z.index.val < 2 then (if z.index.val < 1 then 0 else 40) else (if z.index.val < 3 then 26 else 32)) else (if z.index.val < 6 then (if z.index.val < 5 then 48 else 44) else (if z.index.val < 7 then 20 else 36))) : Fin 68)

private theorem child9_generator_mem (z : N9.state.Row)
    (hz : N9.state.CentralInvolution generators_full z) :
    ∀ j, N9.normalGenerators j ∈ (states (child9 z)).kernel := by
  have ht := N9.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N9.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N9.normalGenerators j ∈ N40.kernel
    intro j
    have he : ∀ j : Fin 2, N9.normalGenerators j=
        (⟨N40.normalCertificate.rows (((if j.val < 1 then 4 else 3) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N40.normalCertificate _
  · change ∀ j, N9.normalGenerators j ∈ N26.kernel
    intro j
    have he : ∀ j : Fin 2, N9.normalGenerators j=
        (⟨N26.normalCertificate.rows (((if j.val < 1 then 5 else 2) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N26.normalCertificate _
  · change ∀ j, N9.normalGenerators j ∈ N32.kernel
    intro j
    have he : ∀ j : Fin 2, N9.normalGenerators j=
        (⟨N32.normalCertificate.rows (((if j.val < 1 then 5 else 2) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N32.normalCertificate _
  · change ∀ j, N9.normalGenerators j ∈ N48.kernel
    intro j
    have he : ∀ j : Fin 2, N9.normalGenerators j=
        (⟨N48.normalCertificate.rows (((if j.val < 1 then 4 else 3) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N48.normalCertificate _
  · change ∀ j, N9.normalGenerators j ∈ N44.kernel
    intro j
    have he : ∀ j : Fin 2, N9.normalGenerators j=
        (⟨N44.normalCertificate.rows (((if j.val < 1 then 4 else 3) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N44.normalCertificate _
  · change ∀ j, N9.normalGenerators j ∈ N20.kernel
    intro j
    have he : ∀ j : Fin 2, N9.normalGenerators j=
        (⟨N20.normalCertificate.rows (((if j.val < 1 then 5 else 2) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N20.normalCertificate _
  · change ∀ j, N9.normalGenerators j ∈ N36.kernel
    intro j
    have he : ∀ j : Fin 2, N9.normalGenerators j=
        (⟨N36.normalCertificate.rows (((if j.val < 1 then 4 else 3) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N36.normalCertificate _

private theorem child9_lift_mem (z : N9.state.Row)
    (hz : N9.state.CentralInvolution generators_full z) :
    N9.cosets.representatives z.index ∈ (states (child9 z)).kernel := by
  have ht := N9.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N9.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N9.cosets.representatives 1 ∈ N40.kernel
    have he : N9.cosets.representatives 1=
        (⟨N40.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N40.normalCertificate _
  · change N9.cosets.representatives 2 ∈ N26.kernel
    have he : N9.cosets.representatives 2=
        (⟨N26.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N26.normalCertificate _
  · change N9.cosets.representatives 3 ∈ N32.kernel
    have he : N9.cosets.representatives 3=
        (⟨N32.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N32.normalCertificate _
  · change N9.cosets.representatives 4 ∈ N48.kernel
    have he : N9.cosets.representatives 4=
        (⟨N48.normalCertificate.rows 5⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N48.normalCertificate _
  · change N9.cosets.representatives 5 ∈ N44.kernel
    have he : N9.cosets.representatives 5=
        (⟨N44.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N44.normalCertificate _
  · change N9.cosets.representatives 6 ∈ N20.kernel
    have he : N9.cosets.representatives 6=
        (⟨N20.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N20.normalCertificate _
  · change N9.cosets.representatives 7 ∈ N36.kernel
    have he : N9.cosets.representatives 7=
        (⟨N36.normalCertificate.rows 5⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N36.normalCertificate _

private theorem child9_card (z : N9.state.Row)
    (hz : N9.state.CentralInvolution generators_full z) :
    Nat.card (states (child9 z)).kernel=Nat.card N9.kernel*2 := by
  have ht := N9.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N9.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N40.kernel=Nat.card N9.kernel*2
    rw [N40.kernel_card,N9.kernel_card]
  · change Nat.card N26.kernel=Nat.card N9.kernel*2
    rw [N26.kernel_card,N9.kernel_card]
  · change Nat.card N32.kernel=Nat.card N9.kernel*2
    rw [N32.kernel_card,N9.kernel_card]
  · change Nat.card N48.kernel=Nat.card N9.kernel*2
    rw [N48.kernel_card,N9.kernel_card]
  · change Nat.card N44.kernel=Nat.card N9.kernel*2
    rw [N44.kernel_card,N9.kernel_card]
  · change Nat.card N20.kernel=Nat.card N9.kernel*2
    rw [N20.kernel_card,N9.kernel_card]
  · change Nat.card N36.kernel=Nat.card N9.kernel*2
    rw [N36.kernel_card,N9.kernel_card]

private def child10 (z : N10.state.Row) : Fin 68 :=
  ((if z.index.val < 4 then (if z.index.val < 2 then (if z.index.val < 1 then 0 else 41) else (if z.index.val < 3 then 33 else 27)) else (if z.index.val < 6 then (if z.index.val < 5 then 45 else 49) else (if z.index.val < 7 then 20 else 37))) : Fin 68)

private theorem child10_generator_mem (z : N10.state.Row)
    (hz : N10.state.CentralInvolution generators_full z) :
    ∀ j, N10.normalGenerators j ∈ (states (child10 z)).kernel := by
  have ht := N10.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N10.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N10.normalGenerators j ∈ N41.kernel
    intro j
    have he : ∀ j : Fin 1, N10.normalGenerators j=
        (⟨N41.normalCertificate.rows ((4 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N41.normalCertificate _
  · change ∀ j, N10.normalGenerators j ∈ N33.kernel
    intro j
    have he : ∀ j : Fin 1, N10.normalGenerators j=
        (⟨N33.normalCertificate.rows ((4 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N33.normalCertificate _
  · change ∀ j, N10.normalGenerators j ∈ N27.kernel
    intro j
    have he : ∀ j : Fin 1, N10.normalGenerators j=
        (⟨N27.normalCertificate.rows ((4 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N27.normalCertificate _
  · change ∀ j, N10.normalGenerators j ∈ N45.kernel
    intro j
    have he : ∀ j : Fin 1, N10.normalGenerators j=
        (⟨N45.normalCertificate.rows ((4 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N45.normalCertificate _
  · change ∀ j, N10.normalGenerators j ∈ N49.kernel
    intro j
    have he : ∀ j : Fin 1, N10.normalGenerators j=
        (⟨N49.normalCertificate.rows ((4 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N49.normalCertificate _
  · change ∀ j, N10.normalGenerators j ∈ N20.kernel
    intro j
    have he : ∀ j : Fin 1, N10.normalGenerators j=
        (⟨N20.normalCertificate.rows ((4 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N20.normalCertificate _
  · change ∀ j, N10.normalGenerators j ∈ N37.kernel
    intro j
    have he : ∀ j : Fin 1, N10.normalGenerators j=
        (⟨N37.normalCertificate.rows ((4 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N37.normalCertificate _

private theorem child10_lift_mem (z : N10.state.Row)
    (hz : N10.state.CentralInvolution generators_full z) :
    N10.cosets.representatives z.index ∈ (states (child10 z)).kernel := by
  have ht := N10.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N10.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N10.cosets.representatives 1 ∈ N41.kernel
    have he : N10.cosets.representatives 1=
        (⟨N41.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N41.normalCertificate _
  · change N10.cosets.representatives 2 ∈ N33.kernel
    have he : N10.cosets.representatives 2=
        (⟨N33.normalCertificate.rows 2⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N33.normalCertificate _
  · change N10.cosets.representatives 3 ∈ N27.kernel
    have he : N10.cosets.representatives 3=
        (⟨N27.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N27.normalCertificate _
  · change N10.cosets.representatives 4 ∈ N45.kernel
    have he : N10.cosets.representatives 4=
        (⟨N45.normalCertificate.rows 5⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N45.normalCertificate _
  · change N10.cosets.representatives 5 ∈ N49.kernel
    have he : N10.cosets.representatives 5=
        (⟨N49.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N49.normalCertificate _
  · change N10.cosets.representatives 6 ∈ N20.kernel
    have he : N10.cosets.representatives 6=
        (⟨N20.normalCertificate.rows 2⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N20.normalCertificate _
  · change N10.cosets.representatives 7 ∈ N37.kernel
    have he : N10.cosets.representatives 7=
        (⟨N37.normalCertificate.rows 5⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N37.normalCertificate _

private theorem child10_card (z : N10.state.Row)
    (hz : N10.state.CentralInvolution generators_full z) :
    Nat.card (states (child10 z)).kernel=Nat.card N10.kernel*2 := by
  have ht := N10.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N10.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N41.kernel=Nat.card N10.kernel*2
    rw [N41.kernel_card,N10.kernel_card]
  · change Nat.card N33.kernel=Nat.card N10.kernel*2
    rw [N33.kernel_card,N10.kernel_card]
  · change Nat.card N27.kernel=Nat.card N10.kernel*2
    rw [N27.kernel_card,N10.kernel_card]
  · change Nat.card N45.kernel=Nat.card N10.kernel*2
    rw [N45.kernel_card,N10.kernel_card]
  · change Nat.card N49.kernel=Nat.card N10.kernel*2
    rw [N49.kernel_card,N10.kernel_card]
  · change Nat.card N20.kernel=Nat.card N10.kernel*2
    rw [N20.kernel_card,N10.kernel_card]
  · change Nat.card N37.kernel=Nat.card N10.kernel*2
    rw [N37.kernel_card,N10.kernel_card]

private def child11 (z : N11.state.Row) : Fin 68 :=
  ((if z.index.val < 4 then (if z.index.val < 2 then (if z.index.val < 1 then 0 else 42) else (if z.index.val < 3 then 33 else 26)) else (if z.index.val < 6 then (if z.index.val < 5 then 46 else 50) else (if z.index.val < 7 then 21 else 38))) : Fin 68)

private theorem child11_generator_mem (z : N11.state.Row)
    (hz : N11.state.CentralInvolution generators_full z) :
    ∀ j, N11.normalGenerators j ∈ (states (child11 z)).kernel := by
  have ht := N11.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N11.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N11.normalGenerators j ∈ N42.kernel
    intro j
    have he : ∀ j : Fin 2, N11.normalGenerators j=
        (⟨N42.normalCertificate.rows (((if j.val < 1 then 4 else 3) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N42.normalCertificate _
  · change ∀ j, N11.normalGenerators j ∈ N33.kernel
    intro j
    have he : ∀ j : Fin 2, N11.normalGenerators j=
        (⟨N33.normalCertificate.rows (((if j.val < 1 then 5 else 2) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N33.normalCertificate _
  · change ∀ j, N11.normalGenerators j ∈ N26.kernel
    intro j
    have he : ∀ j : Fin 2, N11.normalGenerators j=
        (⟨N26.normalCertificate.rows (((if j.val < 1 then 4 else 3) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N26.normalCertificate _
  · change ∀ j, N11.normalGenerators j ∈ N46.kernel
    intro j
    have he : ∀ j : Fin 2, N11.normalGenerators j=
        (⟨N46.normalCertificate.rows (((if j.val < 1 then 4 else 3) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N46.normalCertificate _
  · change ∀ j, N11.normalGenerators j ∈ N50.kernel
    intro j
    have he : ∀ j : Fin 2, N11.normalGenerators j=
        (⟨N50.normalCertificate.rows (((if j.val < 1 then 4 else 3) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N50.normalCertificate _
  · change ∀ j, N11.normalGenerators j ∈ N21.kernel
    intro j
    have he : ∀ j : Fin 2, N11.normalGenerators j=
        (⟨N21.normalCertificate.rows (((if j.val < 1 then 4 else 3) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N21.normalCertificate _
  · change ∀ j, N11.normalGenerators j ∈ N38.kernel
    intro j
    have he : ∀ j : Fin 2, N11.normalGenerators j=
        (⟨N38.normalCertificate.rows (((if j.val < 1 then 4 else 3) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N38.normalCertificate _

private theorem child11_lift_mem (z : N11.state.Row)
    (hz : N11.state.CentralInvolution generators_full z) :
    N11.cosets.representatives z.index ∈ (states (child11 z)).kernel := by
  have ht := N11.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N11.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N11.cosets.representatives 1 ∈ N42.kernel
    have he : N11.cosets.representatives 1=
        (⟨N42.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N42.normalCertificate _
  · change N11.cosets.representatives 2 ∈ N33.kernel
    have he : N11.cosets.representatives 2=
        (⟨N33.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N33.normalCertificate _
  · change N11.cosets.representatives 3 ∈ N26.kernel
    have he : N11.cosets.representatives 3=
        (⟨N26.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N26.normalCertificate _
  · change N11.cosets.representatives 4 ∈ N46.kernel
    have he : N11.cosets.representatives 4=
        (⟨N46.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N46.normalCertificate _
  · change N11.cosets.representatives 5 ∈ N50.kernel
    have he : N11.cosets.representatives 5=
        (⟨N50.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N50.normalCertificate _
  · change N11.cosets.representatives 6 ∈ N21.kernel
    have he : N11.cosets.representatives 6=
        (⟨N21.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N21.normalCertificate _
  · change N11.cosets.representatives 7 ∈ N38.kernel
    have he : N11.cosets.representatives 7=
        (⟨N38.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N38.normalCertificate _

private theorem child11_card (z : N11.state.Row)
    (hz : N11.state.CentralInvolution generators_full z) :
    Nat.card (states (child11 z)).kernel=Nat.card N11.kernel*2 := by
  have ht := N11.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N11.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N42.kernel=Nat.card N11.kernel*2
    rw [N42.kernel_card,N11.kernel_card]
  · change Nat.card N33.kernel=Nat.card N11.kernel*2
    rw [N33.kernel_card,N11.kernel_card]
  · change Nat.card N26.kernel=Nat.card N11.kernel*2
    rw [N26.kernel_card,N11.kernel_card]
  · change Nat.card N46.kernel=Nat.card N11.kernel*2
    rw [N46.kernel_card,N11.kernel_card]
  · change Nat.card N50.kernel=Nat.card N11.kernel*2
    rw [N50.kernel_card,N11.kernel_card]
  · change Nat.card N21.kernel=Nat.card N11.kernel*2
    rw [N21.kernel_card,N11.kernel_card]
  · change Nat.card N38.kernel=Nat.card N11.kernel*2
    rw [N38.kernel_card,N11.kernel_card]

private def child12 (z : N12.state.Row) : Fin 68 :=
  ((if z.index.val < 4 then (if z.index.val < 2 then (if z.index.val < 1 then 0 else 43) else (if z.index.val < 3 then 21 else 32)) else (if z.index.val < 6 then (if z.index.val < 5 then 27 else 39) else (if z.index.val < 7 then 47 else 51))) : Fin 68)

private theorem child12_generator_mem (z : N12.state.Row)
    (hz : N12.state.CentralInvolution generators_full z) :
    ∀ j, N12.normalGenerators j ∈ (states (child12 z)).kernel := by
  have ht := N12.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N12.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N12.normalGenerators j ∈ N43.kernel
    intro j
    have he : ∀ j : Fin 1, N12.normalGenerators j=
        (⟨N43.normalCertificate.rows ((4 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N43.normalCertificate _
  · change ∀ j, N12.normalGenerators j ∈ N21.kernel
    intro j
    have he : ∀ j : Fin 1, N12.normalGenerators j=
        (⟨N21.normalCertificate.rows ((5 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N21.normalCertificate _
  · change ∀ j, N12.normalGenerators j ∈ N32.kernel
    intro j
    have he : ∀ j : Fin 1, N12.normalGenerators j=
        (⟨N32.normalCertificate.rows ((4 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N32.normalCertificate _
  · change ∀ j, N12.normalGenerators j ∈ N27.kernel
    intro j
    have he : ∀ j : Fin 1, N12.normalGenerators j=
        (⟨N27.normalCertificate.rows ((5 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N27.normalCertificate _
  · change ∀ j, N12.normalGenerators j ∈ N39.kernel
    intro j
    have he : ∀ j : Fin 1, N12.normalGenerators j=
        (⟨N39.normalCertificate.rows ((4 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N39.normalCertificate _
  · change ∀ j, N12.normalGenerators j ∈ N47.kernel
    intro j
    have he : ∀ j : Fin 1, N12.normalGenerators j=
        (⟨N47.normalCertificate.rows ((4 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N47.normalCertificate _
  · change ∀ j, N12.normalGenerators j ∈ N51.kernel
    intro j
    have he : ∀ j : Fin 1, N12.normalGenerators j=
        (⟨N51.normalCertificate.rows ((4 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N51.normalCertificate _

private theorem child12_lift_mem (z : N12.state.Row)
    (hz : N12.state.CentralInvolution generators_full z) :
    N12.cosets.representatives z.index ∈ (states (child12 z)).kernel := by
  have ht := N12.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N12.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N12.cosets.representatives 1 ∈ N43.kernel
    have he : N12.cosets.representatives 1=
        (⟨N43.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N43.normalCertificate _
  · change N12.cosets.representatives 2 ∈ N21.kernel
    have he : N12.cosets.representatives 2=
        (⟨N21.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N21.normalCertificate _
  · change N12.cosets.representatives 3 ∈ N32.kernel
    have he : N12.cosets.representatives 3=
        (⟨N32.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N32.normalCertificate _
  · change N12.cosets.representatives 4 ∈ N27.kernel
    have he : N12.cosets.representatives 4=
        (⟨N27.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N27.normalCertificate _
  · change N12.cosets.representatives 5 ∈ N39.kernel
    have he : N12.cosets.representatives 5=
        (⟨N39.normalCertificate.rows 5⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N39.normalCertificate _
  · change N12.cosets.representatives 6 ∈ N47.kernel
    have he : N12.cosets.representatives 6=
        (⟨N47.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N47.normalCertificate _
  · change N12.cosets.representatives 7 ∈ N51.kernel
    have he : N12.cosets.representatives 7=
        (⟨N51.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N51.normalCertificate _

private theorem child12_card (z : N12.state.Row)
    (hz : N12.state.CentralInvolution generators_full z) :
    Nat.card (states (child12 z)).kernel=Nat.card N12.kernel*2 := by
  have ht := N12.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N12.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N43.kernel=Nat.card N12.kernel*2
    rw [N43.kernel_card,N12.kernel_card]
  · change Nat.card N21.kernel=Nat.card N12.kernel*2
    rw [N21.kernel_card,N12.kernel_card]
  · change Nat.card N32.kernel=Nat.card N12.kernel*2
    rw [N32.kernel_card,N12.kernel_card]
  · change Nat.card N27.kernel=Nat.card N12.kernel*2
    rw [N27.kernel_card,N12.kernel_card]
  · change Nat.card N39.kernel=Nat.card N12.kernel*2
    rw [N39.kernel_card,N12.kernel_card]
  · change Nat.card N47.kernel=Nat.card N12.kernel*2
    rw [N47.kernel_card,N12.kernel_card]
  · change Nat.card N51.kernel=Nat.card N12.kernel*2
    rw [N51.kernel_card,N12.kernel_card]

private def child13 (z : N13.state.Row) : Fin 68 :=
  ((if z.index.val < 4 then (if z.index.val < 2 then (if z.index.val < 1 then 0 else 41) else (if z.index.val < 3 then 46 else 34)) else (if z.index.val < 6 then (if z.index.val < 5 then 28 else 51) else (if z.index.val < 7 then 36 else 22))) : Fin 68)

private theorem child13_generator_mem (z : N13.state.Row)
    (hz : N13.state.CentralInvolution generators_full z) :
    ∀ j, N13.normalGenerators j ∈ (states (child13 z)).kernel := by
  have ht := N13.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N13.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N13.normalGenerators j ∈ N41.kernel
    intro j
    have he : ∀ j : Fin 2, N13.normalGenerators j=
        (⟨N41.normalCertificate.rows (((if j.val < 1 then 6 else 5) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N41.normalCertificate _
  · change ∀ j, N13.normalGenerators j ∈ N46.kernel
    intro j
    have he : ∀ j : Fin 2, N13.normalGenerators j=
        (⟨N46.normalCertificate.rows (((if j.val < 1 then 6 else 5) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N46.normalCertificate _
  · change ∀ j, N13.normalGenerators j ∈ N34.kernel
    intro j
    have he : ∀ j : Fin 2, N13.normalGenerators j=
        (⟨N34.normalCertificate.rows (((if j.val < 1 then 5 else 2) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N34.normalCertificate _
  · change ∀ j, N13.normalGenerators j ∈ N28.kernel
    intro j
    have he : ∀ j : Fin 2, N13.normalGenerators j=
        (⟨N28.normalCertificate.rows (((if j.val < 1 then 5 else 2) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N28.normalCertificate _
  · change ∀ j, N13.normalGenerators j ∈ N51.kernel
    intro j
    have he : ∀ j : Fin 2, N13.normalGenerators j=
        (⟨N51.normalCertificate.rows (((if j.val < 1 then 6 else 5) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N51.normalCertificate _
  · change ∀ j, N13.normalGenerators j ∈ N36.kernel
    intro j
    have he : ∀ j : Fin 2, N13.normalGenerators j=
        (⟨N36.normalCertificate.rows (((if j.val < 1 then 6 else 5) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N36.normalCertificate _
  · change ∀ j, N13.normalGenerators j ∈ N22.kernel
    intro j
    have he : ∀ j : Fin 2, N13.normalGenerators j=
        (⟨N22.normalCertificate.rows (((if j.val < 1 then 5 else 2) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N22.normalCertificate _

private theorem child13_lift_mem (z : N13.state.Row)
    (hz : N13.state.CentralInvolution generators_full z) :
    N13.cosets.representatives z.index ∈ (states (child13 z)).kernel := by
  have ht := N13.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N13.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N13.cosets.representatives 1 ∈ N41.kernel
    have he : N13.cosets.representatives 1=
        (⟨N41.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N41.normalCertificate _
  · change N13.cosets.representatives 2 ∈ N46.kernel
    have he : N13.cosets.representatives 2=
        (⟨N46.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N46.normalCertificate _
  · change N13.cosets.representatives 3 ∈ N34.kernel
    have he : N13.cosets.representatives 3=
        (⟨N34.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N34.normalCertificate _
  · change N13.cosets.representatives 4 ∈ N28.kernel
    have he : N13.cosets.representatives 4=
        (⟨N28.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N28.normalCertificate _
  · change N13.cosets.representatives 5 ∈ N51.kernel
    have he : N13.cosets.representatives 5=
        (⟨N51.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N51.normalCertificate _
  · change N13.cosets.representatives 6 ∈ N36.kernel
    have he : N13.cosets.representatives 6=
        (⟨N36.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N36.normalCertificate _
  · change N13.cosets.representatives 7 ∈ N22.kernel
    have he : N13.cosets.representatives 7=
        (⟨N22.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N22.normalCertificate _

private theorem child13_card (z : N13.state.Row)
    (hz : N13.state.CentralInvolution generators_full z) :
    Nat.card (states (child13 z)).kernel=Nat.card N13.kernel*2 := by
  have ht := N13.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N13.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N41.kernel=Nat.card N13.kernel*2
    rw [N41.kernel_card,N13.kernel_card]
  · change Nat.card N46.kernel=Nat.card N13.kernel*2
    rw [N46.kernel_card,N13.kernel_card]
  · change Nat.card N34.kernel=Nat.card N13.kernel*2
    rw [N34.kernel_card,N13.kernel_card]
  · change Nat.card N28.kernel=Nat.card N13.kernel*2
    rw [N28.kernel_card,N13.kernel_card]
  · change Nat.card N51.kernel=Nat.card N13.kernel*2
    rw [N51.kernel_card,N13.kernel_card]
  · change Nat.card N36.kernel=Nat.card N13.kernel*2
    rw [N36.kernel_card,N13.kernel_card]
  · change Nat.card N22.kernel=Nat.card N13.kernel*2
    rw [N22.kernel_card,N13.kernel_card]

private def child14 (z : N14.state.Row) : Fin 68 :=
  ((if z.index.val < 4 then (if z.index.val < 2 then (if z.index.val < 1 then 0 else 40) else (if z.index.val < 3 then 50 else 35)) else (if z.index.val < 6 then (if z.index.val < 5 then 29 else 47) else (if z.index.val < 7 then 37 else 22))) : Fin 68)

private theorem child14_generator_mem (z : N14.state.Row)
    (hz : N14.state.CentralInvolution generators_full z) :
    ∀ j, N14.normalGenerators j ∈ (states (child14 z)).kernel := by
  have ht := N14.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N14.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N14.normalGenerators j ∈ N40.kernel
    intro j
    have he : ∀ j : Fin 1, N14.normalGenerators j=
        (⟨N40.normalCertificate.rows ((6 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N40.normalCertificate _
  · change ∀ j, N14.normalGenerators j ∈ N50.kernel
    intro j
    have he : ∀ j : Fin 1, N14.normalGenerators j=
        (⟨N50.normalCertificate.rows ((6 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N50.normalCertificate _
  · change ∀ j, N14.normalGenerators j ∈ N35.kernel
    intro j
    have he : ∀ j : Fin 1, N14.normalGenerators j=
        (⟨N35.normalCertificate.rows ((4 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N35.normalCertificate _
  · change ∀ j, N14.normalGenerators j ∈ N29.kernel
    intro j
    have he : ∀ j : Fin 1, N14.normalGenerators j=
        (⟨N29.normalCertificate.rows ((4 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N29.normalCertificate _
  · change ∀ j, N14.normalGenerators j ∈ N47.kernel
    intro j
    have he : ∀ j : Fin 1, N14.normalGenerators j=
        (⟨N47.normalCertificate.rows ((6 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N47.normalCertificate _
  · change ∀ j, N14.normalGenerators j ∈ N37.kernel
    intro j
    have he : ∀ j : Fin 1, N14.normalGenerators j=
        (⟨N37.normalCertificate.rows ((6 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N37.normalCertificate _
  · change ∀ j, N14.normalGenerators j ∈ N22.kernel
    intro j
    have he : ∀ j : Fin 1, N14.normalGenerators j=
        (⟨N22.normalCertificate.rows ((4 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N22.normalCertificate _

private theorem child14_lift_mem (z : N14.state.Row)
    (hz : N14.state.CentralInvolution generators_full z) :
    N14.cosets.representatives z.index ∈ (states (child14 z)).kernel := by
  have ht := N14.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N14.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N14.cosets.representatives 1 ∈ N40.kernel
    have he : N14.cosets.representatives 1=
        (⟨N40.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N40.normalCertificate _
  · change N14.cosets.representatives 2 ∈ N50.kernel
    have he : N14.cosets.representatives 2=
        (⟨N50.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N50.normalCertificate _
  · change N14.cosets.representatives 3 ∈ N35.kernel
    have he : N14.cosets.representatives 3=
        (⟨N35.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N35.normalCertificate _
  · change N14.cosets.representatives 4 ∈ N29.kernel
    have he : N14.cosets.representatives 4=
        (⟨N29.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N29.normalCertificate _
  · change N14.cosets.representatives 5 ∈ N47.kernel
    have he : N14.cosets.representatives 5=
        (⟨N47.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N47.normalCertificate _
  · change N14.cosets.representatives 6 ∈ N37.kernel
    have he : N14.cosets.representatives 6=
        (⟨N37.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N37.normalCertificate _
  · change N14.cosets.representatives 7 ∈ N22.kernel
    have he : N14.cosets.representatives 7=
        (⟨N22.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N22.normalCertificate _

private theorem child14_card (z : N14.state.Row)
    (hz : N14.state.CentralInvolution generators_full z) :
    Nat.card (states (child14 z)).kernel=Nat.card N14.kernel*2 := by
  have ht := N14.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N14.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N40.kernel=Nat.card N14.kernel*2
    rw [N40.kernel_card,N14.kernel_card]
  · change Nat.card N50.kernel=Nat.card N14.kernel*2
    rw [N50.kernel_card,N14.kernel_card]
  · change Nat.card N35.kernel=Nat.card N14.kernel*2
    rw [N35.kernel_card,N14.kernel_card]
  · change Nat.card N29.kernel=Nat.card N14.kernel*2
    rw [N29.kernel_card,N14.kernel_card]
  · change Nat.card N47.kernel=Nat.card N14.kernel*2
    rw [N47.kernel_card,N14.kernel_card]
  · change Nat.card N37.kernel=Nat.card N14.kernel*2
    rw [N37.kernel_card,N14.kernel_card]
  · change Nat.card N22.kernel=Nat.card N14.kernel*2
    rw [N22.kernel_card,N14.kernel_card]

private def child15 (z : N15.state.Row) : Fin 68 :=
  ((if z.index.val < 4 then (if z.index.val < 2 then (if z.index.val < 1 then 0 else 43) else (if z.index.val < 3 then 38 else 35)) else (if z.index.val < 6 then (if z.index.val < 5 then 28 else 23) else (if z.index.val < 7 then 44 else 49))) : Fin 68)

private theorem child15_generator_mem (z : N15.state.Row)
    (hz : N15.state.CentralInvolution generators_full z) :
    ∀ j, N15.normalGenerators j ∈ (states (child15 z)).kernel := by
  have ht := N15.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N15.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N15.normalGenerators j ∈ N43.kernel
    intro j
    have he : ∀ j : Fin 1, N15.normalGenerators j=
        (⟨N43.normalCertificate.rows ((6 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N43.normalCertificate _
  · change ∀ j, N15.normalGenerators j ∈ N38.kernel
    intro j
    have he : ∀ j : Fin 1, N15.normalGenerators j=
        (⟨N38.normalCertificate.rows ((6 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N38.normalCertificate _
  · change ∀ j, N15.normalGenerators j ∈ N35.kernel
    intro j
    have he : ∀ j : Fin 1, N15.normalGenerators j=
        (⟨N35.normalCertificate.rows ((5 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N35.normalCertificate _
  · change ∀ j, N15.normalGenerators j ∈ N28.kernel
    intro j
    have he : ∀ j : Fin 1, N15.normalGenerators j=
        (⟨N28.normalCertificate.rows ((4 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N28.normalCertificate _
  · change ∀ j, N15.normalGenerators j ∈ N23.kernel
    intro j
    have he : ∀ j : Fin 1, N15.normalGenerators j=
        (⟨N23.normalCertificate.rows ((4 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N23.normalCertificate _
  · change ∀ j, N15.normalGenerators j ∈ N44.kernel
    intro j
    have he : ∀ j : Fin 1, N15.normalGenerators j=
        (⟨N44.normalCertificate.rows ((6 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N44.normalCertificate _
  · change ∀ j, N15.normalGenerators j ∈ N49.kernel
    intro j
    have he : ∀ j : Fin 1, N15.normalGenerators j=
        (⟨N49.normalCertificate.rows ((6 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N49.normalCertificate _

private theorem child15_lift_mem (z : N15.state.Row)
    (hz : N15.state.CentralInvolution generators_full z) :
    N15.cosets.representatives z.index ∈ (states (child15 z)).kernel := by
  have ht := N15.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N15.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N15.cosets.representatives 1 ∈ N43.kernel
    have he : N15.cosets.representatives 1=
        (⟨N43.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N43.normalCertificate _
  · change N15.cosets.representatives 2 ∈ N38.kernel
    have he : N15.cosets.representatives 2=
        (⟨N38.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N38.normalCertificate _
  · change N15.cosets.representatives 3 ∈ N35.kernel
    have he : N15.cosets.representatives 3=
        (⟨N35.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N35.normalCertificate _
  · change N15.cosets.representatives 4 ∈ N28.kernel
    have he : N15.cosets.representatives 4=
        (⟨N28.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N28.normalCertificate _
  · change N15.cosets.representatives 5 ∈ N23.kernel
    have he : N15.cosets.representatives 5=
        (⟨N23.normalCertificate.rows 2⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N23.normalCertificate _
  · change N15.cosets.representatives 6 ∈ N44.kernel
    have he : N15.cosets.representatives 6=
        (⟨N44.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N44.normalCertificate _
  · change N15.cosets.representatives 7 ∈ N49.kernel
    have he : N15.cosets.representatives 7=
        (⟨N49.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N49.normalCertificate _

private theorem child15_card (z : N15.state.Row)
    (hz : N15.state.CentralInvolution generators_full z) :
    Nat.card (states (child15 z)).kernel=Nat.card N15.kernel*2 := by
  have ht := N15.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N15.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N43.kernel=Nat.card N15.kernel*2
    rw [N43.kernel_card,N15.kernel_card]
  · change Nat.card N38.kernel=Nat.card N15.kernel*2
    rw [N38.kernel_card,N15.kernel_card]
  · change Nat.card N35.kernel=Nat.card N15.kernel*2
    rw [N35.kernel_card,N15.kernel_card]
  · change Nat.card N28.kernel=Nat.card N15.kernel*2
    rw [N28.kernel_card,N15.kernel_card]
  · change Nat.card N23.kernel=Nat.card N15.kernel*2
    rw [N23.kernel_card,N15.kernel_card]
  · change Nat.card N44.kernel=Nat.card N15.kernel*2
    rw [N44.kernel_card,N15.kernel_card]
  · change Nat.card N49.kernel=Nat.card N15.kernel*2
    rw [N49.kernel_card,N15.kernel_card]

private def child16 (z : N16.state.Row) : Fin 68 :=
  ((if z.index.val < 4 then (if z.index.val < 2 then (if z.index.val < 1 then 0 else 42) else (if z.index.val < 3 then 34 else 29)) else (if z.index.val < 6 then (if z.index.val < 5 then 45 else 48) else (if z.index.val < 7 then 23 else 39))) : Fin 68)

private theorem child16_generator_mem (z : N16.state.Row)
    (hz : N16.state.CentralInvolution generators_full z) :
    ∀ j, N16.normalGenerators j ∈ (states (child16 z)).kernel := by
  have ht := N16.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N16.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N16.normalGenerators j ∈ N42.kernel
    intro j
    have he : ∀ j : Fin 2, N16.normalGenerators j=
        (⟨N42.normalCertificate.rows (((if j.val < 1 then 6 else 5) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N42.normalCertificate _
  · change ∀ j, N16.normalGenerators j ∈ N34.kernel
    intro j
    have he : ∀ j : Fin 2, N16.normalGenerators j=
        (⟨N34.normalCertificate.rows (((if j.val < 1 then 4 else 3) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N34.normalCertificate _
  · change ∀ j, N16.normalGenerators j ∈ N29.kernel
    intro j
    have he : ∀ j : Fin 2, N16.normalGenerators j=
        (⟨N29.normalCertificate.rows (((if j.val < 1 then 5 else 2) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N29.normalCertificate _
  · change ∀ j, N16.normalGenerators j ∈ N45.kernel
    intro j
    have he : ∀ j : Fin 2, N16.normalGenerators j=
        (⟨N45.normalCertificate.rows (((if j.val < 1 then 6 else 5) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N45.normalCertificate _
  · change ∀ j, N16.normalGenerators j ∈ N48.kernel
    intro j
    have he : ∀ j : Fin 2, N16.normalGenerators j=
        (⟨N48.normalCertificate.rows (((if j.val < 1 then 6 else 5) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N48.normalCertificate _
  · change ∀ j, N16.normalGenerators j ∈ N23.kernel
    intro j
    have he : ∀ j : Fin 2, N16.normalGenerators j=
        (⟨N23.normalCertificate.rows (((if j.val < 1 then 5 else 2) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N23.normalCertificate _
  · change ∀ j, N16.normalGenerators j ∈ N39.kernel
    intro j
    have he : ∀ j : Fin 2, N16.normalGenerators j=
        (⟨N39.normalCertificate.rows (((if j.val < 1 then 6 else 5) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N39.normalCertificate _

private theorem child16_lift_mem (z : N16.state.Row)
    (hz : N16.state.CentralInvolution generators_full z) :
    N16.cosets.representatives z.index ∈ (states (child16 z)).kernel := by
  have ht := N16.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N16.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N16.cosets.representatives 1 ∈ N42.kernel
    have he : N16.cosets.representatives 1=
        (⟨N42.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N42.normalCertificate _
  · change N16.cosets.representatives 2 ∈ N34.kernel
    have he : N16.cosets.representatives 2=
        (⟨N34.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N34.normalCertificate _
  · change N16.cosets.representatives 3 ∈ N29.kernel
    have he : N16.cosets.representatives 3=
        (⟨N29.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N29.normalCertificate _
  · change N16.cosets.representatives 4 ∈ N45.kernel
    have he : N16.cosets.representatives 4=
        (⟨N45.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N45.normalCertificate _
  · change N16.cosets.representatives 5 ∈ N48.kernel
    have he : N16.cosets.representatives 5=
        (⟨N48.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N48.normalCertificate _
  · change N16.cosets.representatives 6 ∈ N23.kernel
    have he : N16.cosets.representatives 6=
        (⟨N23.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N23.normalCertificate _
  · change N16.cosets.representatives 7 ∈ N39.kernel
    have he : N16.cosets.representatives 7=
        (⟨N39.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N39.normalCertificate _

private theorem child16_card (z : N16.state.Row)
    (hz : N16.state.CentralInvolution generators_full z) :
    Nat.card (states (child16 z)).kernel=Nat.card N16.kernel*2 := by
  have ht := N16.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N16.state.centralRowTests generators_full ⟨(0 : Fin 8)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N42.kernel=Nat.card N16.kernel*2
    rw [N42.kernel_card,N16.kernel_card]
  · change Nat.card N34.kernel=Nat.card N16.kernel*2
    rw [N34.kernel_card,N16.kernel_card]
  · change Nat.card N29.kernel=Nat.card N16.kernel*2
    rw [N29.kernel_card,N16.kernel_card]
  · change Nat.card N45.kernel=Nat.card N16.kernel*2
    rw [N45.kernel_card,N16.kernel_card]
  · change Nat.card N48.kernel=Nat.card N16.kernel*2
    rw [N48.kernel_card,N16.kernel_card]
  · change Nat.card N23.kernel=Nat.card N16.kernel*2
    rw [N23.kernel_card,N16.kernel_card]
  · change Nat.card N39.kernel=Nat.card N16.kernel*2
    rw [N39.kernel_card,N16.kernel_card]

private def child17 (z : N17.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 52) else (if z.index.val < 3 then 53 else 54)) : Fin 68)

private theorem child17_generator_mem (z : N17.state.Row)
    (hz : N17.state.CentralInvolution generators_full z) :
    ∀ j, N17.normalGenerators j ∈ (states (child17 z)).kernel := by
  have ht := N17.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N17.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N17.normalGenerators j ∈ N52.kernel
    intro j
    have he : ∀ j : Fin 3, N17.normalGenerators j=
        (⟨N52.normalCertificate.rows (((if j.val < 1 then 12 else (if j.val < 2 then 13 else 1)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N52.normalCertificate _
  · change ∀ j, N17.normalGenerators j ∈ N53.kernel
    intro j
    have he : ∀ j : Fin 3, N17.normalGenerators j=
        (⟨N53.normalCertificate.rows (((if j.val < 1 then 12 else (if j.val < 2 then 13 else 1)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N53.normalCertificate _
  · change ∀ j, N17.normalGenerators j ∈ N54.kernel
    intro j
    have he : ∀ j : Fin 3, N17.normalGenerators j=
        (⟨N54.normalCertificate.rows (((if j.val < 1 then 12 else (if j.val < 2 then 13 else 1)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N54.normalCertificate _

private theorem child17_lift_mem (z : N17.state.Row)
    (hz : N17.state.CentralInvolution generators_full z) :
    N17.cosets.representatives z.index ∈ (states (child17 z)).kernel := by
  have ht := N17.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N17.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N17.cosets.representatives 1 ∈ N52.kernel
    have he : N17.cosets.representatives 1=
        (⟨N52.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N52.normalCertificate _
  · change N17.cosets.representatives 2 ∈ N53.kernel
    have he : N17.cosets.representatives 2=
        (⟨N53.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N53.normalCertificate _
  · change N17.cosets.representatives 3 ∈ N54.kernel
    have he : N17.cosets.representatives 3=
        (⟨N54.normalCertificate.rows 5⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N54.normalCertificate _

private theorem child17_card (z : N17.state.Row)
    (hz : N17.state.CentralInvolution generators_full z) :
    Nat.card (states (child17 z)).kernel=Nat.card N17.kernel*2 := by
  have ht := N17.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N17.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N52.kernel=Nat.card N17.kernel*2
    rw [N52.kernel_card,N17.kernel_card]
  · change Nat.card N53.kernel=Nat.card N17.kernel*2
    rw [N53.kernel_card,N17.kernel_card]
  · change Nat.card N54.kernel=Nat.card N17.kernel*2
    rw [N54.kernel_card,N17.kernel_card]

private def child18 (z : N18.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 56) else (if z.index.val < 3 then 52 else 55)) : Fin 68)

private theorem child18_generator_mem (z : N18.state.Row)
    (hz : N18.state.CentralInvolution generators_full z) :
    ∀ j, N18.normalGenerators j ∈ (states (child18 z)).kernel := by
  have ht := N18.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N18.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N18.normalGenerators j ∈ N56.kernel
    intro j
    have he : ∀ j : Fin 3, N18.normalGenerators j=
        (⟨N56.normalCertificate.rows (((if j.val < 1 then 14 else (if j.val < 2 then 5 else 3)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N56.normalCertificate _
  · change ∀ j, N18.normalGenerators j ∈ N52.kernel
    intro j
    have he : ∀ j : Fin 3, N18.normalGenerators j=
        (⟨N52.normalCertificate.rows (((if j.val < 1 then 12 else (if j.val < 2 then 11 else 7)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N52.normalCertificate _
  · change ∀ j, N18.normalGenerators j ∈ N55.kernel
    intro j
    have he : ∀ j : Fin 3, N18.normalGenerators j=
        (⟨N55.normalCertificate.rows (((if j.val < 1 then 14 else (if j.val < 2 then 5 else 3)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N55.normalCertificate _

private theorem child18_lift_mem (z : N18.state.Row)
    (hz : N18.state.CentralInvolution generators_full z) :
    N18.cosets.representatives z.index ∈ (states (child18 z)).kernel := by
  have ht := N18.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N18.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N18.cosets.representatives 1 ∈ N56.kernel
    have he : N18.cosets.representatives 1=
        (⟨N56.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N56.normalCertificate _
  · change N18.cosets.representatives 2 ∈ N52.kernel
    have he : N18.cosets.representatives 2=
        (⟨N52.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N52.normalCertificate _
  · change N18.cosets.representatives 3 ∈ N55.kernel
    have he : N18.cosets.representatives 3=
        (⟨N55.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N55.normalCertificate _

private theorem child18_card (z : N18.state.Row)
    (hz : N18.state.CentralInvolution generators_full z) :
    Nat.card (states (child18 z)).kernel=Nat.card N18.kernel*2 := by
  have ht := N18.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N18.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N56.kernel=Nat.card N18.kernel*2
    rw [N56.kernel_card,N18.kernel_card]
  · change Nat.card N52.kernel=Nat.card N18.kernel*2
    rw [N52.kernel_card,N18.kernel_card]
  · change Nat.card N55.kernel=Nat.card N18.kernel*2
    rw [N55.kernel_card,N18.kernel_card]

private def child19 (z : N19.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 52) else (if z.index.val < 3 then 58 else 57)) : Fin 68)

private theorem child19_generator_mem (z : N19.state.Row)
    (hz : N19.state.CentralInvolution generators_full z) :
    ∀ j, N19.normalGenerators j ∈ (states (child19 z)).kernel := by
  have ht := N19.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N19.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N19.normalGenerators j ∈ N52.kernel
    intro j
    have he : ∀ j : Fin 2, N19.normalGenerators j=
        (⟨N52.normalCertificate.rows (((if j.val < 1 then 12 else 9) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N52.normalCertificate _
  · change ∀ j, N19.normalGenerators j ∈ N58.kernel
    intro j
    have he : ∀ j : Fin 2, N19.normalGenerators j=
        (⟨N58.normalCertificate.rows (((if j.val < 1 then 14 else 4) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N58.normalCertificate _
  · change ∀ j, N19.normalGenerators j ∈ N57.kernel
    intro j
    have he : ∀ j : Fin 2, N19.normalGenerators j=
        (⟨N57.normalCertificate.rows (((if j.val < 1 then 14 else 4) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N57.normalCertificate _

private theorem child19_lift_mem (z : N19.state.Row)
    (hz : N19.state.CentralInvolution generators_full z) :
    N19.cosets.representatives z.index ∈ (states (child19 z)).kernel := by
  have ht := N19.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N19.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N19.cosets.representatives 1 ∈ N52.kernel
    have he : N19.cosets.representatives 1=
        (⟨N52.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N52.normalCertificate _
  · change N19.cosets.representatives 2 ∈ N58.kernel
    have he : N19.cosets.representatives 2=
        (⟨N58.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N58.normalCertificate _
  · change N19.cosets.representatives 3 ∈ N57.kernel
    have he : N19.cosets.representatives 3=
        (⟨N57.normalCertificate.rows 10⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N57.normalCertificate _

private theorem child19_card (z : N19.state.Row)
    (hz : N19.state.CentralInvolution generators_full z) :
    Nat.card (states (child19 z)).kernel=Nat.card N19.kernel*2 := by
  have ht := N19.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N19.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N52.kernel=Nat.card N19.kernel*2
    rw [N52.kernel_card,N19.kernel_card]
  · change Nat.card N58.kernel=Nat.card N19.kernel*2
    rw [N58.kernel_card,N19.kernel_card]
  · change Nat.card N57.kernel=Nat.card N19.kernel*2
    rw [N57.kernel_card,N19.kernel_card]

private def child20 (z : N20.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 55) else (if z.index.val < 3 then 53 else 57)) : Fin 68)

private theorem child20_generator_mem (z : N20.state.Row)
    (hz : N20.state.CentralInvolution generators_full z) :
    ∀ j, N20.normalGenerators j ∈ (states (child20 z)).kernel := by
  have ht := N20.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N20.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N20.normalGenerators j ∈ N55.kernel
    intro j
    have he : ∀ j : Fin 2, N20.normalGenerators j=
        (⟨N55.normalCertificate.rows (((if j.val < 1 then 14 else 9) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N55.normalCertificate _
  · change ∀ j, N20.normalGenerators j ∈ N53.kernel
    intro j
    have he : ∀ j : Fin 2, N20.normalGenerators j=
        (⟨N53.normalCertificate.rows (((if j.val < 1 then 12 else 11) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N53.normalCertificate _
  · change ∀ j, N20.normalGenerators j ∈ N57.kernel
    intro j
    have he : ∀ j : Fin 2, N20.normalGenerators j=
        (⟨N57.normalCertificate.rows (((if j.val < 1 then 14 else 9) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N57.normalCertificate _

private theorem child20_lift_mem (z : N20.state.Row)
    (hz : N20.state.CentralInvolution generators_full z) :
    N20.cosets.representatives z.index ∈ (states (child20 z)).kernel := by
  have ht := N20.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N20.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N20.cosets.representatives 1 ∈ N55.kernel
    have he : N20.cosets.representatives 1=
        (⟨N55.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N55.normalCertificate _
  · change N20.cosets.representatives 2 ∈ N53.kernel
    have he : N20.cosets.representatives 2=
        (⟨N53.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N53.normalCertificate _
  · change N20.cosets.representatives 3 ∈ N57.kernel
    have he : N20.cosets.representatives 3=
        (⟨N57.normalCertificate.rows 10⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N57.normalCertificate _

private theorem child20_card (z : N20.state.Row)
    (hz : N20.state.CentralInvolution generators_full z) :
    Nat.card (states (child20 z)).kernel=Nat.card N20.kernel*2 := by
  have ht := N20.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N20.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N55.kernel=Nat.card N20.kernel*2
    rw [N55.kernel_card,N20.kernel_card]
  · change Nat.card N53.kernel=Nat.card N20.kernel*2
    rw [N53.kernel_card,N20.kernel_card]
  · change Nat.card N57.kernel=Nat.card N20.kernel*2
    rw [N57.kernel_card,N20.kernel_card]

private def child21 (z : N21.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 56) else (if z.index.val < 3 then 53 else 58)) : Fin 68)

private theorem child21_generator_mem (z : N21.state.Row)
    (hz : N21.state.CentralInvolution generators_full z) :
    ∀ j, N21.normalGenerators j ∈ (states (child21 z)).kernel := by
  have ht := N21.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N21.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N21.normalGenerators j ∈ N56.kernel
    intro j
    have he : ∀ j : Fin 2, N21.normalGenerators j=
        (⟨N56.normalCertificate.rows (((if j.val < 1 then 14 else 8) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N56.normalCertificate _
  · change ∀ j, N21.normalGenerators j ∈ N53.kernel
    intro j
    have he : ∀ j : Fin 2, N21.normalGenerators j=
        (⟨N53.normalCertificate.rows (((if j.val < 1 then 12 else 9) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N53.normalCertificate _
  · change ∀ j, N21.normalGenerators j ∈ N58.kernel
    intro j
    have he : ∀ j : Fin 2, N21.normalGenerators j=
        (⟨N58.normalCertificate.rows (((if j.val < 1 then 14 else 8) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N58.normalCertificate _

private theorem child21_lift_mem (z : N21.state.Row)
    (hz : N21.state.CentralInvolution generators_full z) :
    N21.cosets.representatives z.index ∈ (states (child21 z)).kernel := by
  have ht := N21.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N21.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N21.cosets.representatives 1 ∈ N56.kernel
    have he : N21.cosets.representatives 1=
        (⟨N56.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N56.normalCertificate _
  · change N21.cosets.representatives 2 ∈ N53.kernel
    have he : N21.cosets.representatives 2=
        (⟨N53.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N53.normalCertificate _
  · change N21.cosets.representatives 3 ∈ N58.kernel
    have he : N21.cosets.representatives 3=
        (⟨N58.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N58.normalCertificate _

private theorem child21_card (z : N21.state.Row)
    (hz : N21.state.CentralInvolution generators_full z) :
    Nat.card (states (child21 z)).kernel=Nat.card N21.kernel*2 := by
  have ht := N21.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N21.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N56.kernel=Nat.card N21.kernel*2
    rw [N56.kernel_card,N21.kernel_card]
  · change Nat.card N53.kernel=Nat.card N21.kernel*2
    rw [N53.kernel_card,N21.kernel_card]
  · change Nat.card N58.kernel=Nat.card N21.kernel*2
    rw [N58.kernel_card,N21.kernel_card]

private def child22 (z : N22.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 55) else (if z.index.val < 3 then 58 else 54)) : Fin 68)

private theorem child22_generator_mem (z : N22.state.Row)
    (hz : N22.state.CentralInvolution generators_full z) :
    ∀ j, N22.normalGenerators j ∈ (states (child22 z)).kernel := by
  have ht := N22.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N22.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N22.normalGenerators j ∈ N55.kernel
    intro j
    have he : ∀ j : Fin 2, N22.normalGenerators j=
        (⟨N55.normalCertificate.rows (((if j.val < 1 then 14 else 13) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N55.normalCertificate _
  · change ∀ j, N22.normalGenerators j ∈ N58.kernel
    intro j
    have he : ∀ j : Fin 2, N22.normalGenerators j=
        (⟨N58.normalCertificate.rows (((if j.val < 1 then 14 else 13) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N58.normalCertificate _
  · change ∀ j, N22.normalGenerators j ∈ N54.kernel
    intro j
    have he : ∀ j : Fin 2, N22.normalGenerators j=
        (⟨N54.normalCertificate.rows (((if j.val < 1 then 12 else 11) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N54.normalCertificate _

private theorem child22_lift_mem (z : N22.state.Row)
    (hz : N22.state.CentralInvolution generators_full z) :
    N22.cosets.representatives z.index ∈ (states (child22 z)).kernel := by
  have ht := N22.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N22.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N22.cosets.representatives 1 ∈ N55.kernel
    have he : N22.cosets.representatives 1=
        (⟨N55.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N55.normalCertificate _
  · change N22.cosets.representatives 2 ∈ N58.kernel
    have he : N22.cosets.representatives 2=
        (⟨N58.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N58.normalCertificate _
  · change N22.cosets.representatives 3 ∈ N54.kernel
    have he : N22.cosets.representatives 3=
        (⟨N54.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N54.normalCertificate _

private theorem child22_card (z : N22.state.Row)
    (hz : N22.state.CentralInvolution generators_full z) :
    Nat.card (states (child22 z)).kernel=Nat.card N22.kernel*2 := by
  have ht := N22.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N22.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N55.kernel=Nat.card N22.kernel*2
    rw [N55.kernel_card,N22.kernel_card]
  · change Nat.card N58.kernel=Nat.card N22.kernel*2
    rw [N58.kernel_card,N22.kernel_card]
  · change Nat.card N54.kernel=Nat.card N22.kernel*2
    rw [N54.kernel_card,N22.kernel_card]

private def child23 (z : N23.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 56) else (if z.index.val < 3 then 54 else 57)) : Fin 68)

private theorem child23_generator_mem (z : N23.state.Row)
    (hz : N23.state.CentralInvolution generators_full z) :
    ∀ j, N23.normalGenerators j ∈ (states (child23 z)).kernel := by
  have ht := N23.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N23.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N23.normalGenerators j ∈ N56.kernel
    intro j
    have he : ∀ j : Fin 2, N23.normalGenerators j=
        (⟨N56.normalCertificate.rows (((if j.val < 1 then 14 else 12) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N56.normalCertificate _
  · change ∀ j, N23.normalGenerators j ∈ N54.kernel
    intro j
    have he : ∀ j : Fin 2, N23.normalGenerators j=
        (⟨N54.normalCertificate.rows (((if j.val < 1 then 12 else 9) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N54.normalCertificate _
  · change ∀ j, N23.normalGenerators j ∈ N57.kernel
    intro j
    have he : ∀ j : Fin 2, N23.normalGenerators j=
        (⟨N57.normalCertificate.rows (((if j.val < 1 then 14 else 12) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N57.normalCertificate _

private theorem child23_lift_mem (z : N23.state.Row)
    (hz : N23.state.CentralInvolution generators_full z) :
    N23.cosets.representatives z.index ∈ (states (child23 z)).kernel := by
  have ht := N23.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N23.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N23.cosets.representatives 1 ∈ N56.kernel
    have he : N23.cosets.representatives 1=
        (⟨N56.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N56.normalCertificate _
  · change N23.cosets.representatives 2 ∈ N54.kernel
    have he : N23.cosets.representatives 2=
        (⟨N54.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N54.normalCertificate _
  · change N23.cosets.representatives 3 ∈ N57.kernel
    have he : N23.cosets.representatives 3=
        (⟨N57.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N57.normalCertificate _

private theorem child23_card (z : N23.state.Row)
    (hz : N23.state.CentralInvolution generators_full z) :
    Nat.card (states (child23 z)).kernel=Nat.card N23.kernel*2 := by
  have ht := N23.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N23.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N56.kernel=Nat.card N23.kernel*2
    rw [N56.kernel_card,N23.kernel_card]
  · change Nat.card N54.kernel=Nat.card N23.kernel*2
    rw [N54.kernel_card,N23.kernel_card]
  · change Nat.card N57.kernel=Nat.card N23.kernel*2
    rw [N57.kernel_card,N23.kernel_card]

private def child24 (z : N24.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 52) else (if z.index.val < 3 then 59 else 60)) : Fin 68)

private theorem child24_generator_mem (z : N24.state.Row)
    (hz : N24.state.CentralInvolution generators_full z) :
    ∀ j, N24.normalGenerators j ∈ (states (child24 z)).kernel := by
  have ht := N24.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N24.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N24.normalGenerators j ∈ N52.kernel
    intro j
    have he : ∀ j : Fin 2, N24.normalGenerators j=
        (⟨N52.normalCertificate.rows (((if j.val < 1 then 13 else 11) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N52.normalCertificate _
  · change ∀ j, N24.normalGenerators j ∈ N59.kernel
    intro j
    have he : ∀ j : Fin 2, N24.normalGenerators j=
        (⟨N59.normalCertificate.rows (((if j.val < 1 then 14 else 5) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N59.normalCertificate _
  · change ∀ j, N24.normalGenerators j ∈ N60.kernel
    intro j
    have he : ∀ j : Fin 2, N24.normalGenerators j=
        (⟨N60.normalCertificate.rows (((if j.val < 1 then 14 else 5) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N60.normalCertificate _

private theorem child24_lift_mem (z : N24.state.Row)
    (hz : N24.state.CentralInvolution generators_full z) :
    N24.cosets.representatives z.index ∈ (states (child24 z)).kernel := by
  have ht := N24.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N24.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N24.cosets.representatives 1 ∈ N52.kernel
    have he : N24.cosets.representatives 1=
        (⟨N52.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N52.normalCertificate _
  · change N24.cosets.representatives 2 ∈ N59.kernel
    have he : N24.cosets.representatives 2=
        (⟨N59.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N59.normalCertificate _
  · change N24.cosets.representatives 3 ∈ N60.kernel
    have he : N24.cosets.representatives 3=
        (⟨N60.normalCertificate.rows 10⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N60.normalCertificate _

private theorem child24_card (z : N24.state.Row)
    (hz : N24.state.CentralInvolution generators_full z) :
    Nat.card (states (child24 z)).kernel=Nat.card N24.kernel*2 := by
  have ht := N24.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N24.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N52.kernel=Nat.card N24.kernel*2
    rw [N52.kernel_card,N24.kernel_card]
  · change Nat.card N59.kernel=Nat.card N24.kernel*2
    rw [N59.kernel_card,N24.kernel_card]
  · change Nat.card N60.kernel=Nat.card N24.kernel*2
    rw [N60.kernel_card,N24.kernel_card]

private def child25 (z : N25.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 61) else (if z.index.val < 3 then 52 else 62)) : Fin 68)

private theorem child25_generator_mem (z : N25.state.Row)
    (hz : N25.state.CentralInvolution generators_full z) :
    ∀ j, N25.normalGenerators j ∈ (states (child25 z)).kernel := by
  have ht := N25.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N25.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N25.normalGenerators j ∈ N61.kernel
    intro j
    have he : ∀ j : Fin 2, N25.normalGenerators j=
        (⟨N61.normalCertificate.rows (((if j.val < 1 then 14 else 4) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N61.normalCertificate _
  · change ∀ j, N25.normalGenerators j ∈ N52.kernel
    intro j
    have he : ∀ j : Fin 2, N25.normalGenerators j=
        (⟨N52.normalCertificate.rows (((if j.val < 1 then 13 else 8) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N52.normalCertificate _
  · change ∀ j, N25.normalGenerators j ∈ N62.kernel
    intro j
    have he : ∀ j : Fin 2, N25.normalGenerators j=
        (⟨N62.normalCertificate.rows (((if j.val < 1 then 14 else 4) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N62.normalCertificate _

private theorem child25_lift_mem (z : N25.state.Row)
    (hz : N25.state.CentralInvolution generators_full z) :
    N25.cosets.representatives z.index ∈ (states (child25 z)).kernel := by
  have ht := N25.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N25.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N25.cosets.representatives 1 ∈ N61.kernel
    have he : N25.cosets.representatives 1=
        (⟨N61.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N61.normalCertificate _
  · change N25.cosets.representatives 2 ∈ N52.kernel
    have he : N25.cosets.representatives 2=
        (⟨N52.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N52.normalCertificate _
  · change N25.cosets.representatives 3 ∈ N62.kernel
    have he : N25.cosets.representatives 3=
        (⟨N62.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N62.normalCertificate _

private theorem child25_card (z : N25.state.Row)
    (hz : N25.state.CentralInvolution generators_full z) :
    Nat.card (states (child25 z)).kernel=Nat.card N25.kernel*2 := by
  have ht := N25.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N25.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N61.kernel=Nat.card N25.kernel*2
    rw [N61.kernel_card,N25.kernel_card]
  · change Nat.card N52.kernel=Nat.card N25.kernel*2
    rw [N52.kernel_card,N25.kernel_card]
  · change Nat.card N62.kernel=Nat.card N25.kernel*2
    rw [N62.kernel_card,N25.kernel_card]

private def child26 (z : N26.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 61) else (if z.index.val < 3 then 53 else 59)) : Fin 68)

private theorem child26_generator_mem (z : N26.state.Row)
    (hz : N26.state.CentralInvolution generators_full z) :
    ∀ j, N26.normalGenerators j ∈ (states (child26 z)).kernel := by
  have ht := N26.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N26.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N26.normalGenerators j ∈ N61.kernel
    intro j
    have he : ∀ j : Fin 3, N26.normalGenerators j=
        (⟨N61.normalCertificate.rows (((if j.val < 1 then 14 else (if j.val < 2 then 9 else 7)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N61.normalCertificate _
  · change ∀ j, N26.normalGenerators j ∈ N53.kernel
    intro j
    have he : ∀ j : Fin 3, N26.normalGenerators j=
        (⟨N53.normalCertificate.rows (((if j.val < 1 then 13 else (if j.val < 2 then 11 else 6)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N53.normalCertificate _
  · change ∀ j, N26.normalGenerators j ∈ N59.kernel
    intro j
    have he : ∀ j : Fin 3, N26.normalGenerators j=
        (⟨N59.normalCertificate.rows (((if j.val < 1 then 14 else (if j.val < 2 then 9 else 7)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N59.normalCertificate _

private theorem child26_lift_mem (z : N26.state.Row)
    (hz : N26.state.CentralInvolution generators_full z) :
    N26.cosets.representatives z.index ∈ (states (child26 z)).kernel := by
  have ht := N26.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N26.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N26.cosets.representatives 1 ∈ N61.kernel
    have he : N26.cosets.representatives 1=
        (⟨N61.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N61.normalCertificate _
  · change N26.cosets.representatives 2 ∈ N53.kernel
    have he : N26.cosets.representatives 2=
        (⟨N53.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N53.normalCertificate _
  · change N26.cosets.representatives 3 ∈ N59.kernel
    have he : N26.cosets.representatives 3=
        (⟨N59.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N59.normalCertificate _

private theorem child26_card (z : N26.state.Row)
    (hz : N26.state.CentralInvolution generators_full z) :
    Nat.card (states (child26 z)).kernel=Nat.card N26.kernel*2 := by
  have ht := N26.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N26.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N61.kernel=Nat.card N26.kernel*2
    rw [N61.kernel_card,N26.kernel_card]
  · change Nat.card N53.kernel=Nat.card N26.kernel*2
    rw [N53.kernel_card,N26.kernel_card]
  · change Nat.card N59.kernel=Nat.card N26.kernel*2
    rw [N59.kernel_card,N26.kernel_card]

private def child27 (z : N27.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 62) else (if z.index.val < 3 then 53 else 60)) : Fin 68)

private theorem child27_generator_mem (z : N27.state.Row)
    (hz : N27.state.CentralInvolution generators_full z) :
    ∀ j, N27.normalGenerators j ∈ (states (child27 z)).kernel := by
  have ht := N27.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N27.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N27.normalGenerators j ∈ N62.kernel
    intro j
    have he : ∀ j : Fin 2, N27.normalGenerators j=
        (⟨N62.normalCertificate.rows (((if j.val < 1 then 14 else 8) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N62.normalCertificate _
  · change ∀ j, N27.normalGenerators j ∈ N53.kernel
    intro j
    have he : ∀ j : Fin 2, N27.normalGenerators j=
        (⟨N53.normalCertificate.rows (((if j.val < 1 then 13 else 8) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N53.normalCertificate _
  · change ∀ j, N27.normalGenerators j ∈ N60.kernel
    intro j
    have he : ∀ j : Fin 2, N27.normalGenerators j=
        (⟨N60.normalCertificate.rows (((if j.val < 1 then 14 else 8) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N60.normalCertificate _

private theorem child27_lift_mem (z : N27.state.Row)
    (hz : N27.state.CentralInvolution generators_full z) :
    N27.cosets.representatives z.index ∈ (states (child27 z)).kernel := by
  have ht := N27.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N27.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N27.cosets.representatives 1 ∈ N62.kernel
    have he : N27.cosets.representatives 1=
        (⟨N62.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N62.normalCertificate _
  · change N27.cosets.representatives 2 ∈ N53.kernel
    have he : N27.cosets.representatives 2=
        (⟨N53.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N53.normalCertificate _
  · change N27.cosets.representatives 3 ∈ N60.kernel
    have he : N27.cosets.representatives 3=
        (⟨N60.normalCertificate.rows 10⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N60.normalCertificate _

private theorem child27_card (z : N27.state.Row)
    (hz : N27.state.CentralInvolution generators_full z) :
    Nat.card (states (child27 z)).kernel=Nat.card N27.kernel*2 := by
  have ht := N27.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N27.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N62.kernel=Nat.card N27.kernel*2
    rw [N62.kernel_card,N27.kernel_card]
  · change Nat.card N53.kernel=Nat.card N27.kernel*2
    rw [N53.kernel_card,N27.kernel_card]
  · change Nat.card N60.kernel=Nat.card N27.kernel*2
    rw [N60.kernel_card,N27.kernel_card]

private def child28 (z : N28.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 62) else (if z.index.val < 3 then 59 else 54)) : Fin 68)

private theorem child28_generator_mem (z : N28.state.Row)
    (hz : N28.state.CentralInvolution generators_full z) :
    ∀ j, N28.normalGenerators j ∈ (states (child28 z)).kernel := by
  have ht := N28.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N28.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N28.normalGenerators j ∈ N62.kernel
    intro j
    have he : ∀ j : Fin 2, N28.normalGenerators j=
        (⟨N62.normalCertificate.rows (((if j.val < 1 then 14 else 13) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N62.normalCertificate _
  · change ∀ j, N28.normalGenerators j ∈ N59.kernel
    intro j
    have he : ∀ j : Fin 2, N28.normalGenerators j=
        (⟨N59.normalCertificate.rows (((if j.val < 1 then 14 else 13) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N59.normalCertificate _
  · change ∀ j, N28.normalGenerators j ∈ N54.kernel
    intro j
    have he : ∀ j : Fin 2, N28.normalGenerators j=
        (⟨N54.normalCertificate.rows (((if j.val < 1 then 13 else 11) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N54.normalCertificate _

private theorem child28_lift_mem (z : N28.state.Row)
    (hz : N28.state.CentralInvolution generators_full z) :
    N28.cosets.representatives z.index ∈ (states (child28 z)).kernel := by
  have ht := N28.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N28.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N28.cosets.representatives 1 ∈ N62.kernel
    have he : N28.cosets.representatives 1=
        (⟨N62.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N62.normalCertificate _
  · change N28.cosets.representatives 2 ∈ N59.kernel
    have he : N28.cosets.representatives 2=
        (⟨N59.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N59.normalCertificate _
  · change N28.cosets.representatives 3 ∈ N54.kernel
    have he : N28.cosets.representatives 3=
        (⟨N54.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N54.normalCertificate _

private theorem child28_card (z : N28.state.Row)
    (hz : N28.state.CentralInvolution generators_full z) :
    Nat.card (states (child28 z)).kernel=Nat.card N28.kernel*2 := by
  have ht := N28.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N28.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N62.kernel=Nat.card N28.kernel*2
    rw [N62.kernel_card,N28.kernel_card]
  · change Nat.card N59.kernel=Nat.card N28.kernel*2
    rw [N59.kernel_card,N28.kernel_card]
  · change Nat.card N54.kernel=Nat.card N28.kernel*2
    rw [N54.kernel_card,N28.kernel_card]

private def child29 (z : N29.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 61) else (if z.index.val < 3 then 54 else 60)) : Fin 68)

private theorem child29_generator_mem (z : N29.state.Row)
    (hz : N29.state.CentralInvolution generators_full z) :
    ∀ j, N29.normalGenerators j ∈ (states (child29 z)).kernel := by
  have ht := N29.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N29.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N29.normalGenerators j ∈ N61.kernel
    intro j
    have he : ∀ j : Fin 2, N29.normalGenerators j=
        (⟨N61.normalCertificate.rows (((if j.val < 1 then 14 else 12) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N61.normalCertificate _
  · change ∀ j, N29.normalGenerators j ∈ N54.kernel
    intro j
    have he : ∀ j : Fin 2, N29.normalGenerators j=
        (⟨N54.normalCertificate.rows (((if j.val < 1 then 13 else 8) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N54.normalCertificate _
  · change ∀ j, N29.normalGenerators j ∈ N60.kernel
    intro j
    have he : ∀ j : Fin 2, N29.normalGenerators j=
        (⟨N60.normalCertificate.rows (((if j.val < 1 then 14 else 12) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N60.normalCertificate _

private theorem child29_lift_mem (z : N29.state.Row)
    (hz : N29.state.CentralInvolution generators_full z) :
    N29.cosets.representatives z.index ∈ (states (child29 z)).kernel := by
  have ht := N29.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N29.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N29.cosets.representatives 1 ∈ N61.kernel
    have he : N29.cosets.representatives 1=
        (⟨N61.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N61.normalCertificate _
  · change N29.cosets.representatives 2 ∈ N54.kernel
    have he : N29.cosets.representatives 2=
        (⟨N54.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N54.normalCertificate _
  · change N29.cosets.representatives 3 ∈ N60.kernel
    have he : N29.cosets.representatives 3=
        (⟨N60.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N60.normalCertificate _

private theorem child29_card (z : N29.state.Row)
    (hz : N29.state.CentralInvolution generators_full z) :
    Nat.card (states (child29 z)).kernel=Nat.card N29.kernel*2 := by
  have ht := N29.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N29.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N61.kernel=Nat.card N29.kernel*2
    rw [N61.kernel_card,N29.kernel_card]
  · change Nat.card N54.kernel=Nat.card N29.kernel*2
    rw [N54.kernel_card,N29.kernel_card]
  · change Nat.card N60.kernel=Nat.card N29.kernel*2
    rw [N60.kernel_card,N29.kernel_card]

private def child30 (z : N30.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 52) else (if z.index.val < 3 then 64 else 63)) : Fin 68)

private theorem child30_generator_mem (z : N30.state.Row)
    (hz : N30.state.CentralInvolution generators_full z) :
    ∀ j, N30.normalGenerators j ∈ (states (child30 z)).kernel := by
  have ht := N30.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N30.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N30.normalGenerators j ∈ N52.kernel
    intro j
    have he : ∀ j : Fin 2, N30.normalGenerators j=
        (⟨N52.normalCertificate.rows (((if j.val < 1 then 14 else 11) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N52.normalCertificate _
  · change ∀ j, N30.normalGenerators j ∈ N64.kernel
    intro j
    have he : ∀ j : Fin 2, N30.normalGenerators j=
        (⟨N64.normalCertificate.rows (((if j.val < 1 then 14 else 5) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N64.normalCertificate _
  · change ∀ j, N30.normalGenerators j ∈ N63.kernel
    intro j
    have he : ∀ j : Fin 2, N30.normalGenerators j=
        (⟨N63.normalCertificate.rows (((if j.val < 1 then 14 else 5) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N63.normalCertificate _

private theorem child30_lift_mem (z : N30.state.Row)
    (hz : N30.state.CentralInvolution generators_full z) :
    N30.cosets.representatives z.index ∈ (states (child30 z)).kernel := by
  have ht := N30.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N30.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N30.cosets.representatives 1 ∈ N52.kernel
    have he : N30.cosets.representatives 1=
        (⟨N52.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N52.normalCertificate _
  · change N30.cosets.representatives 2 ∈ N64.kernel
    have he : N30.cosets.representatives 2=
        (⟨N64.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N64.normalCertificate _
  · change N30.cosets.representatives 3 ∈ N63.kernel
    have he : N30.cosets.representatives 3=
        (⟨N63.normalCertificate.rows 11⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N63.normalCertificate _

private theorem child30_card (z : N30.state.Row)
    (hz : N30.state.CentralInvolution generators_full z) :
    Nat.card (states (child30 z)).kernel=Nat.card N30.kernel*2 := by
  have ht := N30.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N30.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N52.kernel=Nat.card N30.kernel*2
    rw [N52.kernel_card,N30.kernel_card]
  · change Nat.card N64.kernel=Nat.card N30.kernel*2
    rw [N64.kernel_card,N30.kernel_card]
  · change Nat.card N63.kernel=Nat.card N30.kernel*2
    rw [N63.kernel_card,N30.kernel_card]

private def child31 (z : N31.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 66) else (if z.index.val < 3 then 52 else 65)) : Fin 68)

private theorem child31_generator_mem (z : N31.state.Row)
    (hz : N31.state.CentralInvolution generators_full z) :
    ∀ j, N31.normalGenerators j ∈ (states (child31 z)).kernel := by
  have ht := N31.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N31.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N31.normalGenerators j ∈ N66.kernel
    intro j
    have he : ∀ j : Fin 2, N31.normalGenerators j=
        (⟨N66.normalCertificate.rows (((if j.val < 1 then 14 else 4) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N66.normalCertificate _
  · change ∀ j, N31.normalGenerators j ∈ N52.kernel
    intro j
    have he : ∀ j : Fin 2, N31.normalGenerators j=
        (⟨N52.normalCertificate.rows (((if j.val < 1 then 14 else 8) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N52.normalCertificate _
  · change ∀ j, N31.normalGenerators j ∈ N65.kernel
    intro j
    have he : ∀ j : Fin 2, N31.normalGenerators j=
        (⟨N65.normalCertificate.rows (((if j.val < 1 then 14 else 4) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N65.normalCertificate _

private theorem child31_lift_mem (z : N31.state.Row)
    (hz : N31.state.CentralInvolution generators_full z) :
    N31.cosets.representatives z.index ∈ (states (child31 z)).kernel := by
  have ht := N31.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N31.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N31.cosets.representatives 1 ∈ N66.kernel
    have he : N31.cosets.representatives 1=
        (⟨N66.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N66.normalCertificate _
  · change N31.cosets.representatives 2 ∈ N52.kernel
    have he : N31.cosets.representatives 2=
        (⟨N52.normalCertificate.rows 13⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N52.normalCertificate _
  · change N31.cosets.representatives 3 ∈ N65.kernel
    have he : N31.cosets.representatives 3=
        (⟨N65.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N65.normalCertificate _

private theorem child31_card (z : N31.state.Row)
    (hz : N31.state.CentralInvolution generators_full z) :
    Nat.card (states (child31 z)).kernel=Nat.card N31.kernel*2 := by
  have ht := N31.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N31.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N66.kernel=Nat.card N31.kernel*2
    rw [N66.kernel_card,N31.kernel_card]
  · change Nat.card N52.kernel=Nat.card N31.kernel*2
    rw [N52.kernel_card,N31.kernel_card]
  · change Nat.card N65.kernel=Nat.card N31.kernel*2
    rw [N65.kernel_card,N31.kernel_card]

private def child32 (z : N32.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 65) else (if z.index.val < 3 then 53 else 63)) : Fin 68)

private theorem child32_generator_mem (z : N32.state.Row)
    (hz : N32.state.CentralInvolution generators_full z) :
    ∀ j, N32.normalGenerators j ∈ (states (child32 z)).kernel := by
  have ht := N32.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N32.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N32.normalGenerators j ∈ N65.kernel
    intro j
    have he : ∀ j : Fin 2, N32.normalGenerators j=
        (⟨N65.normalCertificate.rows (((if j.val < 1 then 14 else 9) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N65.normalCertificate _
  · change ∀ j, N32.normalGenerators j ∈ N53.kernel
    intro j
    have he : ∀ j : Fin 2, N32.normalGenerators j=
        (⟨N53.normalCertificate.rows (((if j.val < 1 then 14 else 11) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N53.normalCertificate _
  · change ∀ j, N32.normalGenerators j ∈ N63.kernel
    intro j
    have he : ∀ j : Fin 2, N32.normalGenerators j=
        (⟨N63.normalCertificate.rows (((if j.val < 1 then 14 else 9) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N63.normalCertificate _

private theorem child32_lift_mem (z : N32.state.Row)
    (hz : N32.state.CentralInvolution generators_full z) :
    N32.cosets.representatives z.index ∈ (states (child32 z)).kernel := by
  have ht := N32.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N32.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N32.cosets.representatives 1 ∈ N65.kernel
    have he : N32.cosets.representatives 1=
        (⟨N65.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N65.normalCertificate _
  · change N32.cosets.representatives 2 ∈ N53.kernel
    have he : N32.cosets.representatives 2=
        (⟨N53.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N53.normalCertificate _
  · change N32.cosets.representatives 3 ∈ N63.kernel
    have he : N32.cosets.representatives 3=
        (⟨N63.normalCertificate.rows 11⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N63.normalCertificate _

private theorem child32_card (z : N32.state.Row)
    (hz : N32.state.CentralInvolution generators_full z) :
    Nat.card (states (child32 z)).kernel=Nat.card N32.kernel*2 := by
  have ht := N32.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N32.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N65.kernel=Nat.card N32.kernel*2
    rw [N65.kernel_card,N32.kernel_card]
  · change Nat.card N53.kernel=Nat.card N32.kernel*2
    rw [N53.kernel_card,N32.kernel_card]
  · change Nat.card N63.kernel=Nat.card N32.kernel*2
    rw [N63.kernel_card,N32.kernel_card]

private def child33 (z : N33.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 66) else (if z.index.val < 3 then 53 else 64)) : Fin 68)

private theorem child33_generator_mem (z : N33.state.Row)
    (hz : N33.state.CentralInvolution generators_full z) :
    ∀ j, N33.normalGenerators j ∈ (states (child33 z)).kernel := by
  have ht := N33.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N33.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N33.normalGenerators j ∈ N66.kernel
    intro j
    have he : ∀ j : Fin 2, N33.normalGenerators j=
        (⟨N66.normalCertificate.rows (((if j.val < 1 then 14 else 8) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N66.normalCertificate _
  · change ∀ j, N33.normalGenerators j ∈ N53.kernel
    intro j
    have he : ∀ j : Fin 2, N33.normalGenerators j=
        (⟨N53.normalCertificate.rows (((if j.val < 1 then 14 else 8) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N53.normalCertificate _
  · change ∀ j, N33.normalGenerators j ∈ N64.kernel
    intro j
    have he : ∀ j : Fin 2, N33.normalGenerators j=
        (⟨N64.normalCertificate.rows (((if j.val < 1 then 14 else 8) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N64.normalCertificate _

private theorem child33_lift_mem (z : N33.state.Row)
    (hz : N33.state.CentralInvolution generators_full z) :
    N33.cosets.representatives z.index ∈ (states (child33 z)).kernel := by
  have ht := N33.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N33.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N33.cosets.representatives 1 ∈ N66.kernel
    have he : N33.cosets.representatives 1=
        (⟨N66.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N66.normalCertificate _
  · change N33.cosets.representatives 2 ∈ N53.kernel
    have he : N33.cosets.representatives 2=
        (⟨N53.normalCertificate.rows 13⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N53.normalCertificate _
  · change N33.cosets.representatives 3 ∈ N64.kernel
    have he : N33.cosets.representatives 3=
        (⟨N64.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N64.normalCertificate _

private theorem child33_card (z : N33.state.Row)
    (hz : N33.state.CentralInvolution generators_full z) :
    Nat.card (states (child33 z)).kernel=Nat.card N33.kernel*2 := by
  have ht := N33.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N33.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N66.kernel=Nat.card N33.kernel*2
    rw [N66.kernel_card,N33.kernel_card]
  · change Nat.card N53.kernel=Nat.card N33.kernel*2
    rw [N53.kernel_card,N33.kernel_card]
  · change Nat.card N64.kernel=Nat.card N33.kernel*2
    rw [N64.kernel_card,N33.kernel_card]

private def child34 (z : N34.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 66) else (if z.index.val < 3 then 54 else 63)) : Fin 68)

private theorem child34_generator_mem (z : N34.state.Row)
    (hz : N34.state.CentralInvolution generators_full z) :
    ∀ j, N34.normalGenerators j ∈ (states (child34 z)).kernel := by
  have ht := N34.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N34.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N34.normalGenerators j ∈ N66.kernel
    intro j
    have he : ∀ j : Fin 3, N34.normalGenerators j=
        (⟨N66.normalCertificate.rows (((if j.val < 1 then 14 else (if j.val < 2 then 13 else 11)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N66.normalCertificate _
  · change ∀ j, N34.normalGenerators j ∈ N54.kernel
    intro j
    have he : ∀ j : Fin 3, N34.normalGenerators j=
        (⟨N54.normalCertificate.rows (((if j.val < 1 then 14 else (if j.val < 2 then 11 else 5)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N54.normalCertificate _
  · change ∀ j, N34.normalGenerators j ∈ N63.kernel
    intro j
    have he : ∀ j : Fin 3, N34.normalGenerators j=
        (⟨N63.normalCertificate.rows (((if j.val < 1 then 14 else (if j.val < 2 then 13 else 11)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N63.normalCertificate _

private theorem child34_lift_mem (z : N34.state.Row)
    (hz : N34.state.CentralInvolution generators_full z) :
    N34.cosets.representatives z.index ∈ (states (child34 z)).kernel := by
  have ht := N34.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N34.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N34.cosets.representatives 1 ∈ N66.kernel
    have he : N34.cosets.representatives 1=
        (⟨N66.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N66.normalCertificate _
  · change N34.cosets.representatives 2 ∈ N54.kernel
    have he : N34.cosets.representatives 2=
        (⟨N54.normalCertificate.rows 13⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N54.normalCertificate _
  · change N34.cosets.representatives 3 ∈ N63.kernel
    have he : N34.cosets.representatives 3=
        (⟨N63.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N63.normalCertificate _

private theorem child34_card (z : N34.state.Row)
    (hz : N34.state.CentralInvolution generators_full z) :
    Nat.card (states (child34 z)).kernel=Nat.card N34.kernel*2 := by
  have ht := N34.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N34.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N66.kernel=Nat.card N34.kernel*2
    rw [N66.kernel_card,N34.kernel_card]
  · change Nat.card N54.kernel=Nat.card N34.kernel*2
    rw [N54.kernel_card,N34.kernel_card]
  · change Nat.card N63.kernel=Nat.card N34.kernel*2
    rw [N63.kernel_card,N34.kernel_card]

private def child35 (z : N35.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 65) else (if z.index.val < 3 then 64 else 54)) : Fin 68)

private theorem child35_generator_mem (z : N35.state.Row)
    (hz : N35.state.CentralInvolution generators_full z) :
    ∀ j, N35.normalGenerators j ∈ (states (child35 z)).kernel := by
  have ht := N35.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N35.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N35.normalGenerators j ∈ N65.kernel
    intro j
    have he : ∀ j : Fin 2, N35.normalGenerators j=
        (⟨N65.normalCertificate.rows (((if j.val < 1 then 14 else 12) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N65.normalCertificate _
  · change ∀ j, N35.normalGenerators j ∈ N64.kernel
    intro j
    have he : ∀ j : Fin 2, N35.normalGenerators j=
        (⟨N64.normalCertificate.rows (((if j.val < 1 then 14 else 12) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N64.normalCertificate _
  · change ∀ j, N35.normalGenerators j ∈ N54.kernel
    intro j
    have he : ∀ j : Fin 2, N35.normalGenerators j=
        (⟨N54.normalCertificate.rows (((if j.val < 1 then 14 else 8) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N54.normalCertificate _

private theorem child35_lift_mem (z : N35.state.Row)
    (hz : N35.state.CentralInvolution generators_full z) :
    N35.cosets.representatives z.index ∈ (states (child35 z)).kernel := by
  have ht := N35.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N35.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N35.cosets.representatives 1 ∈ N65.kernel
    have he : N35.cosets.representatives 1=
        (⟨N65.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N65.normalCertificate _
  · change N35.cosets.representatives 2 ∈ N64.kernel
    have he : N35.cosets.representatives 2=
        (⟨N64.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N64.normalCertificate _
  · change N35.cosets.representatives 3 ∈ N54.kernel
    have he : N35.cosets.representatives 3=
        (⟨N54.normalCertificate.rows 13⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N54.normalCertificate _

private theorem child35_card (z : N35.state.Row)
    (hz : N35.state.CentralInvolution generators_full z) :
    Nat.card (states (child35 z)).kernel=Nat.card N35.kernel*2 := by
  have ht := N35.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N35.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N65.kernel=Nat.card N35.kernel*2
    rw [N65.kernel_card,N35.kernel_card]
  · change Nat.card N64.kernel=Nat.card N35.kernel*2
    rw [N64.kernel_card,N35.kernel_card]
  · change Nat.card N54.kernel=Nat.card N35.kernel*2
    rw [N54.kernel_card,N35.kernel_card]

private def child36 (z : N36.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 55) else (if z.index.val < 3 then 59 else 63)) : Fin 68)

private theorem child36_generator_mem (z : N36.state.Row)
    (hz : N36.state.CentralInvolution generators_full z) :
    ∀ j, N36.normalGenerators j ∈ (states (child36 z)).kernel := by
  have ht := N36.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N36.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N36.normalGenerators j ∈ N55.kernel
    intro j
    have he : ∀ j : Fin 3, N36.normalGenerators j=
        (⟨N55.normalCertificate.rows (((if j.val < 1 then 5 else (if j.val < 2 then 2 else 9)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N55.normalCertificate _
  · change ∀ j, N36.normalGenerators j ∈ N59.kernel
    intro j
    have he : ∀ j : Fin 3, N36.normalGenerators j=
        (⟨N59.normalCertificate.rows (((if j.val < 1 then 5 else (if j.val < 2 then 2 else 9)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N59.normalCertificate _
  · change ∀ j, N36.normalGenerators j ∈ N63.kernel
    intro j
    have he : ∀ j : Fin 3, N36.normalGenerators j=
        (⟨N63.normalCertificate.rows (((if j.val < 1 then 5 else (if j.val < 2 then 2 else 9)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N63.normalCertificate _

private theorem child36_lift_mem (z : N36.state.Row)
    (hz : N36.state.CentralInvolution generators_full z) :
    N36.cosets.representatives z.index ∈ (states (child36 z)).kernel := by
  have ht := N36.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N36.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N36.cosets.representatives 1 ∈ N55.kernel
    have he : N36.cosets.representatives 1=
        (⟨N55.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N55.normalCertificate _
  · change N36.cosets.representatives 2 ∈ N59.kernel
    have he : N36.cosets.representatives 2=
        (⟨N59.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N59.normalCertificate _
  · change N36.cosets.representatives 3 ∈ N63.kernel
    have he : N36.cosets.representatives 3=
        (⟨N63.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N63.normalCertificate _

private theorem child36_card (z : N36.state.Row)
    (hz : N36.state.CentralInvolution generators_full z) :
    Nat.card (states (child36 z)).kernel=Nat.card N36.kernel*2 := by
  have ht := N36.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N36.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N55.kernel=Nat.card N36.kernel*2
    rw [N55.kernel_card,N36.kernel_card]
  · change Nat.card N59.kernel=Nat.card N36.kernel*2
    rw [N59.kernel_card,N36.kernel_card]
  · change Nat.card N63.kernel=Nat.card N36.kernel*2
    rw [N63.kernel_card,N36.kernel_card]

private def child37 (z : N37.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 55) else (if z.index.val < 3 then 64 else 60)) : Fin 68)

private theorem child37_generator_mem (z : N37.state.Row)
    (hz : N37.state.CentralInvolution generators_full z) :
    ∀ j, N37.normalGenerators j ∈ (states (child37 z)).kernel := by
  have ht := N37.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N37.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N37.normalGenerators j ∈ N55.kernel
    intro j
    have he : ∀ j : Fin 3, N37.normalGenerators j=
        (⟨N55.normalCertificate.rows (((if j.val < 1 then 5 else (if j.val < 2 then 2 else 8)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N55.normalCertificate _
  · change ∀ j, N37.normalGenerators j ∈ N64.kernel
    intro j
    have he : ∀ j : Fin 3, N37.normalGenerators j=
        (⟨N64.normalCertificate.rows (((if j.val < 1 then 5 else (if j.val < 2 then 2 else 8)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N64.normalCertificate _
  · change ∀ j, N37.normalGenerators j ∈ N60.kernel
    intro j
    have he : ∀ j : Fin 3, N37.normalGenerators j=
        (⟨N60.normalCertificate.rows (((if j.val < 1 then 5 else (if j.val < 2 then 2 else 8)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N60.normalCertificate _

private theorem child37_lift_mem (z : N37.state.Row)
    (hz : N37.state.CentralInvolution generators_full z) :
    N37.cosets.representatives z.index ∈ (states (child37 z)).kernel := by
  have ht := N37.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N37.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N37.cosets.representatives 1 ∈ N55.kernel
    have he : N37.cosets.representatives 1=
        (⟨N55.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N55.normalCertificate _
  · change N37.cosets.representatives 2 ∈ N64.kernel
    have he : N37.cosets.representatives 2=
        (⟨N64.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N64.normalCertificate _
  · change N37.cosets.representatives 3 ∈ N60.kernel
    have he : N37.cosets.representatives 3=
        (⟨N60.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N60.normalCertificate _

private theorem child37_card (z : N37.state.Row)
    (hz : N37.state.CentralInvolution generators_full z) :
    Nat.card (states (child37 z)).kernel=Nat.card N37.kernel*2 := by
  have ht := N37.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N37.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N55.kernel=Nat.card N37.kernel*2
    rw [N55.kernel_card,N37.kernel_card]
  · change Nat.card N64.kernel=Nat.card N37.kernel*2
    rw [N64.kernel_card,N37.kernel_card]
  · change Nat.card N60.kernel=Nat.card N37.kernel*2
    rw [N60.kernel_card,N37.kernel_card]

private def child38 (z : N38.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 56) else (if z.index.val < 3 then 64 else 59)) : Fin 68)

private theorem child38_generator_mem (z : N38.state.Row)
    (hz : N38.state.CentralInvolution generators_full z) :
    ∀ j, N38.normalGenerators j ∈ (states (child38 z)).kernel := by
  have ht := N38.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N38.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N38.normalGenerators j ∈ N56.kernel
    intro j
    have he : ∀ j : Fin 3, N38.normalGenerators j=
        (⟨N56.normalCertificate.rows (((if j.val < 1 then 5 else (if j.val < 2 then 2 else 8)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N56.normalCertificate _
  · change ∀ j, N38.normalGenerators j ∈ N64.kernel
    intro j
    have he : ∀ j : Fin 3, N38.normalGenerators j=
        (⟨N64.normalCertificate.rows (((if j.val < 1 then 5 else (if j.val < 2 then 2 else 9)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N64.normalCertificate _
  · change ∀ j, N38.normalGenerators j ∈ N59.kernel
    intro j
    have he : ∀ j : Fin 3, N38.normalGenerators j=
        (⟨N59.normalCertificate.rows (((if j.val < 1 then 5 else (if j.val < 2 then 2 else 8)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N59.normalCertificate _

private theorem child38_lift_mem (z : N38.state.Row)
    (hz : N38.state.CentralInvolution generators_full z) :
    N38.cosets.representatives z.index ∈ (states (child38 z)).kernel := by
  have ht := N38.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N38.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N38.cosets.representatives 1 ∈ N56.kernel
    have he : N38.cosets.representatives 1=
        (⟨N56.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N56.normalCertificate _
  · change N38.cosets.representatives 2 ∈ N64.kernel
    have he : N38.cosets.representatives 2=
        (⟨N64.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N64.normalCertificate _
  · change N38.cosets.representatives 3 ∈ N59.kernel
    have he : N38.cosets.representatives 3=
        (⟨N59.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N59.normalCertificate _

private theorem child38_card (z : N38.state.Row)
    (hz : N38.state.CentralInvolution generators_full z) :
    Nat.card (states (child38 z)).kernel=Nat.card N38.kernel*2 := by
  have ht := N38.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N38.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N56.kernel=Nat.card N38.kernel*2
    rw [N56.kernel_card,N38.kernel_card]
  · change Nat.card N64.kernel=Nat.card N38.kernel*2
    rw [N64.kernel_card,N38.kernel_card]
  · change Nat.card N59.kernel=Nat.card N38.kernel*2
    rw [N59.kernel_card,N38.kernel_card]

private def child39 (z : N39.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 56) else (if z.index.val < 3 then 63 else 60)) : Fin 68)

private theorem child39_generator_mem (z : N39.state.Row)
    (hz : N39.state.CentralInvolution generators_full z) :
    ∀ j, N39.normalGenerators j ∈ (states (child39 z)).kernel := by
  have ht := N39.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N39.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N39.normalGenerators j ∈ N56.kernel
    intro j
    have he : ∀ j : Fin 3, N39.normalGenerators j=
        (⟨N56.normalCertificate.rows (((if j.val < 1 then 5 else (if j.val < 2 then 2 else 9)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N56.normalCertificate _
  · change ∀ j, N39.normalGenerators j ∈ N63.kernel
    intro j
    have he : ∀ j : Fin 3, N39.normalGenerators j=
        (⟨N63.normalCertificate.rows (((if j.val < 1 then 5 else (if j.val < 2 then 2 else 8)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N63.normalCertificate _
  · change ∀ j, N39.normalGenerators j ∈ N60.kernel
    intro j
    have he : ∀ j : Fin 3, N39.normalGenerators j=
        (⟨N60.normalCertificate.rows (((if j.val < 1 then 5 else (if j.val < 2 then 2 else 9)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N60.normalCertificate _

private theorem child39_lift_mem (z : N39.state.Row)
    (hz : N39.state.CentralInvolution generators_full z) :
    N39.cosets.representatives z.index ∈ (states (child39 z)).kernel := by
  have ht := N39.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N39.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N39.cosets.representatives 1 ∈ N56.kernel
    have he : N39.cosets.representatives 1=
        (⟨N56.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N56.normalCertificate _
  · change N39.cosets.representatives 2 ∈ N63.kernel
    have he : N39.cosets.representatives 2=
        (⟨N63.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N63.normalCertificate _
  · change N39.cosets.representatives 3 ∈ N60.kernel
    have he : N39.cosets.representatives 3=
        (⟨N60.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N60.normalCertificate _

private theorem child39_card (z : N39.state.Row)
    (hz : N39.state.CentralInvolution generators_full z) :
    Nat.card (states (child39 z)).kernel=Nat.card N39.kernel*2 := by
  have ht := N39.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N39.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N56.kernel=Nat.card N39.kernel*2
    rw [N56.kernel_card,N39.kernel_card]
  · change Nat.card N63.kernel=Nat.card N39.kernel*2
    rw [N63.kernel_card,N39.kernel_card]
  · change Nat.card N60.kernel=Nat.card N39.kernel*2
    rw [N60.kernel_card,N39.kernel_card]

private def child40 (z : N40.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 61) else (if z.index.val < 3 then 65 else 55)) : Fin 68)

private theorem child40_generator_mem (z : N40.state.Row)
    (hz : N40.state.CentralInvolution generators_full z) :
    ∀ j, N40.normalGenerators j ∈ (states (child40 z)).kernel := by
  have ht := N40.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N40.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N40.normalGenerators j ∈ N61.kernel
    intro j
    have he : ∀ j : Fin 3, N40.normalGenerators j=
        (⟨N61.normalCertificate.rows (((if j.val < 1 then 4 else (if j.val < 2 then 3 else 9)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N61.normalCertificate _
  · change ∀ j, N40.normalGenerators j ∈ N65.kernel
    intro j
    have he : ∀ j : Fin 3, N40.normalGenerators j=
        (⟨N65.normalCertificate.rows (((if j.val < 1 then 4 else (if j.val < 2 then 3 else 9)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N65.normalCertificate _
  · change ∀ j, N40.normalGenerators j ∈ N55.kernel
    intro j
    have he : ∀ j : Fin 3, N40.normalGenerators j=
        (⟨N55.normalCertificate.rows (((if j.val < 1 then 4 else (if j.val < 2 then 3 else 9)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N55.normalCertificate _

private theorem child40_lift_mem (z : N40.state.Row)
    (hz : N40.state.CentralInvolution generators_full z) :
    N40.cosets.representatives z.index ∈ (states (child40 z)).kernel := by
  have ht := N40.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N40.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N40.cosets.representatives 1 ∈ N61.kernel
    have he : N40.cosets.representatives 1=
        (⟨N61.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N61.normalCertificate _
  · change N40.cosets.representatives 2 ∈ N65.kernel
    have he : N40.cosets.representatives 2=
        (⟨N65.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N65.normalCertificate _
  · change N40.cosets.representatives 3 ∈ N55.kernel
    have he : N40.cosets.representatives 3=
        (⟨N55.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N55.normalCertificate _

private theorem child40_card (z : N40.state.Row)
    (hz : N40.state.CentralInvolution generators_full z) :
    Nat.card (states (child40 z)).kernel=Nat.card N40.kernel*2 := by
  have ht := N40.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N40.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N61.kernel=Nat.card N40.kernel*2
    rw [N61.kernel_card,N40.kernel_card]
  · change Nat.card N65.kernel=Nat.card N40.kernel*2
    rw [N65.kernel_card,N40.kernel_card]
  · change Nat.card N55.kernel=Nat.card N40.kernel*2
    rw [N55.kernel_card,N40.kernel_card]

private def child41 (z : N41.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 66) else (if z.index.val < 3 then 62 else 55)) : Fin 68)

private theorem child41_generator_mem (z : N41.state.Row)
    (hz : N41.state.CentralInvolution generators_full z) :
    ∀ j, N41.normalGenerators j ∈ (states (child41 z)).kernel := by
  have ht := N41.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N41.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N41.normalGenerators j ∈ N66.kernel
    intro j
    have he : ∀ j : Fin 3, N41.normalGenerators j=
        (⟨N66.normalCertificate.rows (((if j.val < 1 then 4 else (if j.val < 2 then 3 else 8)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N66.normalCertificate _
  · change ∀ j, N41.normalGenerators j ∈ N62.kernel
    intro j
    have he : ∀ j : Fin 3, N41.normalGenerators j=
        (⟨N62.normalCertificate.rows (((if j.val < 1 then 4 else (if j.val < 2 then 3 else 8)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N62.normalCertificate _
  · change ∀ j, N41.normalGenerators j ∈ N55.kernel
    intro j
    have he : ∀ j : Fin 3, N41.normalGenerators j=
        (⟨N55.normalCertificate.rows (((if j.val < 1 then 4 else (if j.val < 2 then 3 else 8)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N55.normalCertificate _

private theorem child41_lift_mem (z : N41.state.Row)
    (hz : N41.state.CentralInvolution generators_full z) :
    N41.cosets.representatives z.index ∈ (states (child41 z)).kernel := by
  have ht := N41.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N41.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N41.cosets.representatives 1 ∈ N66.kernel
    have he : N41.cosets.representatives 1=
        (⟨N66.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N66.normalCertificate _
  · change N41.cosets.representatives 2 ∈ N62.kernel
    have he : N41.cosets.representatives 2=
        (⟨N62.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N62.normalCertificate _
  · change N41.cosets.representatives 3 ∈ N55.kernel
    have he : N41.cosets.representatives 3=
        (⟨N55.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N55.normalCertificate _

private theorem child41_card (z : N41.state.Row)
    (hz : N41.state.CentralInvolution generators_full z) :
    Nat.card (states (child41 z)).kernel=Nat.card N41.kernel*2 := by
  have ht := N41.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N41.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N66.kernel=Nat.card N41.kernel*2
    rw [N66.kernel_card,N41.kernel_card]
  · change Nat.card N62.kernel=Nat.card N41.kernel*2
    rw [N62.kernel_card,N41.kernel_card]
  · change Nat.card N55.kernel=Nat.card N41.kernel*2
    rw [N55.kernel_card,N41.kernel_card]

private def child42 (z : N42.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 66) else (if z.index.val < 3 then 61 else 56)) : Fin 68)

private theorem child42_generator_mem (z : N42.state.Row)
    (hz : N42.state.CentralInvolution generators_full z) :
    ∀ j, N42.normalGenerators j ∈ (states (child42 z)).kernel := by
  have ht := N42.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N42.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N42.normalGenerators j ∈ N66.kernel
    intro j
    have he : ∀ j : Fin 3, N42.normalGenerators j=
        (⟨N66.normalCertificate.rows (((if j.val < 1 then 4 else (if j.val < 2 then 3 else 9)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N66.normalCertificate _
  · change ∀ j, N42.normalGenerators j ∈ N61.kernel
    intro j
    have he : ∀ j : Fin 3, N42.normalGenerators j=
        (⟨N61.normalCertificate.rows (((if j.val < 1 then 4 else (if j.val < 2 then 3 else 8)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N61.normalCertificate _
  · change ∀ j, N42.normalGenerators j ∈ N56.kernel
    intro j
    have he : ∀ j : Fin 3, N42.normalGenerators j=
        (⟨N56.normalCertificate.rows (((if j.val < 1 then 4 else (if j.val < 2 then 3 else 8)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N56.normalCertificate _

private theorem child42_lift_mem (z : N42.state.Row)
    (hz : N42.state.CentralInvolution generators_full z) :
    N42.cosets.representatives z.index ∈ (states (child42 z)).kernel := by
  have ht := N42.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N42.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N42.cosets.representatives 1 ∈ N66.kernel
    have he : N42.cosets.representatives 1=
        (⟨N66.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N66.normalCertificate _
  · change N42.cosets.representatives 2 ∈ N61.kernel
    have he : N42.cosets.representatives 2=
        (⟨N61.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N61.normalCertificate _
  · change N42.cosets.representatives 3 ∈ N56.kernel
    have he : N42.cosets.representatives 3=
        (⟨N56.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N56.normalCertificate _

private theorem child42_card (z : N42.state.Row)
    (hz : N42.state.CentralInvolution generators_full z) :
    Nat.card (states (child42 z)).kernel=Nat.card N42.kernel*2 := by
  have ht := N42.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N42.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N66.kernel=Nat.card N42.kernel*2
    rw [N66.kernel_card,N42.kernel_card]
  · change Nat.card N61.kernel=Nat.card N42.kernel*2
    rw [N61.kernel_card,N42.kernel_card]
  · change Nat.card N56.kernel=Nat.card N42.kernel*2
    rw [N56.kernel_card,N42.kernel_card]

private def child43 (z : N43.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 56) else (if z.index.val < 3 then 65 else 62)) : Fin 68)

private theorem child43_generator_mem (z : N43.state.Row)
    (hz : N43.state.CentralInvolution generators_full z) :
    ∀ j, N43.normalGenerators j ∈ (states (child43 z)).kernel := by
  have ht := N43.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N43.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N43.normalGenerators j ∈ N56.kernel
    intro j
    have he : ∀ j : Fin 3, N43.normalGenerators j=
        (⟨N56.normalCertificate.rows (((if j.val < 1 then 4 else (if j.val < 2 then 3 else 9)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N56.normalCertificate _
  · change ∀ j, N43.normalGenerators j ∈ N65.kernel
    intro j
    have he : ∀ j : Fin 3, N43.normalGenerators j=
        (⟨N65.normalCertificate.rows (((if j.val < 1 then 4 else (if j.val < 2 then 3 else 8)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N65.normalCertificate _
  · change ∀ j, N43.normalGenerators j ∈ N62.kernel
    intro j
    have he : ∀ j : Fin 3, N43.normalGenerators j=
        (⟨N62.normalCertificate.rows (((if j.val < 1 then 4 else (if j.val < 2 then 3 else 9)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N62.normalCertificate _

private theorem child43_lift_mem (z : N43.state.Row)
    (hz : N43.state.CentralInvolution generators_full z) :
    N43.cosets.representatives z.index ∈ (states (child43 z)).kernel := by
  have ht := N43.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N43.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N43.cosets.representatives 1 ∈ N56.kernel
    have he : N43.cosets.representatives 1=
        (⟨N56.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N56.normalCertificate _
  · change N43.cosets.representatives 2 ∈ N65.kernel
    have he : N43.cosets.representatives 2=
        (⟨N65.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N65.normalCertificate _
  · change N43.cosets.representatives 3 ∈ N62.kernel
    have he : N43.cosets.representatives 3=
        (⟨N62.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N62.normalCertificate _

private theorem child43_card (z : N43.state.Row)
    (hz : N43.state.CentralInvolution generators_full z) :
    Nat.card (states (child43 z)).kernel=Nat.card N43.kernel*2 := by
  have ht := N43.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N43.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N56.kernel=Nat.card N43.kernel*2
    rw [N56.kernel_card,N43.kernel_card]
  · change Nat.card N65.kernel=Nat.card N43.kernel*2
    rw [N65.kernel_card,N43.kernel_card]
  · change Nat.card N62.kernel=Nat.card N43.kernel*2
    rw [N62.kernel_card,N43.kernel_card]

private def child44 (z : N44.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 65) else (if z.index.val < 3 then 59 else 57)) : Fin 68)

private theorem child44_generator_mem (z : N44.state.Row)
    (hz : N44.state.CentralInvolution generators_full z) :
    ∀ j, N44.normalGenerators j ∈ (states (child44 z)).kernel := by
  have ht := N44.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N44.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N44.normalGenerators j ∈ N65.kernel
    intro j
    have he : ∀ j : Fin 2, N44.normalGenerators j=
        (⟨N65.normalCertificate.rows (((if j.val < 1 then 5 else 9) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N65.normalCertificate _
  · change ∀ j, N44.normalGenerators j ∈ N59.kernel
    intro j
    have he : ∀ j : Fin 2, N44.normalGenerators j=
        (⟨N59.normalCertificate.rows (((if j.val < 1 then 4 else 9) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N59.normalCertificate _
  · change ∀ j, N44.normalGenerators j ∈ N57.kernel
    intro j
    have he : ∀ j : Fin 2, N44.normalGenerators j=
        (⟨N57.normalCertificate.rows (((if j.val < 1 then 4 else 9) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N57.normalCertificate _

private theorem child44_lift_mem (z : N44.state.Row)
    (hz : N44.state.CentralInvolution generators_full z) :
    N44.cosets.representatives z.index ∈ (states (child44 z)).kernel := by
  have ht := N44.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N44.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N44.cosets.representatives 1 ∈ N65.kernel
    have he : N44.cosets.representatives 1=
        (⟨N65.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N65.normalCertificate _
  · change N44.cosets.representatives 2 ∈ N59.kernel
    have he : N44.cosets.representatives 2=
        (⟨N59.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N59.normalCertificate _
  · change N44.cosets.representatives 3 ∈ N57.kernel
    have he : N44.cosets.representatives 3=
        (⟨N57.normalCertificate.rows 10⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N57.normalCertificate _

private theorem child44_card (z : N44.state.Row)
    (hz : N44.state.CentralInvolution generators_full z) :
    Nat.card (states (child44 z)).kernel=Nat.card N44.kernel*2 := by
  have ht := N44.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N44.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N65.kernel=Nat.card N44.kernel*2
    rw [N65.kernel_card,N44.kernel_card]
  · change Nat.card N59.kernel=Nat.card N44.kernel*2
    rw [N59.kernel_card,N44.kernel_card]
  · change Nat.card N57.kernel=Nat.card N44.kernel*2
    rw [N57.kernel_card,N44.kernel_card]

private def child45 (z : N45.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 66) else (if z.index.val < 3 then 60 else 57)) : Fin 68)

private theorem child45_generator_mem (z : N45.state.Row)
    (hz : N45.state.CentralInvolution generators_full z) :
    ∀ j, N45.normalGenerators j ∈ (states (child45 z)).kernel := by
  have ht := N45.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N45.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N45.normalGenerators j ∈ N66.kernel
    intro j
    have he : ∀ j : Fin 2, N45.normalGenerators j=
        (⟨N66.normalCertificate.rows (((if j.val < 1 then 5 else 8) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N66.normalCertificate _
  · change ∀ j, N45.normalGenerators j ∈ N60.kernel
    intro j
    have he : ∀ j : Fin 2, N45.normalGenerators j=
        (⟨N60.normalCertificate.rows (((if j.val < 1 then 4 else 8) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N60.normalCertificate _
  · change ∀ j, N45.normalGenerators j ∈ N57.kernel
    intro j
    have he : ∀ j : Fin 2, N45.normalGenerators j=
        (⟨N57.normalCertificate.rows (((if j.val < 1 then 4 else 8) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N57.normalCertificate _

private theorem child45_lift_mem (z : N45.state.Row)
    (hz : N45.state.CentralInvolution generators_full z) :
    N45.cosets.representatives z.index ∈ (states (child45 z)).kernel := by
  have ht := N45.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N45.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N45.cosets.representatives 1 ∈ N66.kernel
    have he : N45.cosets.representatives 1=
        (⟨N66.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N66.normalCertificate _
  · change N45.cosets.representatives 2 ∈ N60.kernel
    have he : N45.cosets.representatives 2=
        (⟨N60.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N60.normalCertificate _
  · change N45.cosets.representatives 3 ∈ N57.kernel
    have he : N45.cosets.representatives 3=
        (⟨N57.normalCertificate.rows 2⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N57.normalCertificate _

private theorem child45_card (z : N45.state.Row)
    (hz : N45.state.CentralInvolution generators_full z) :
    Nat.card (states (child45 z)).kernel=Nat.card N45.kernel*2 := by
  have ht := N45.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N45.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N66.kernel=Nat.card N45.kernel*2
    rw [N66.kernel_card,N45.kernel_card]
  · change Nat.card N60.kernel=Nat.card N45.kernel*2
    rw [N60.kernel_card,N45.kernel_card]
  · change Nat.card N57.kernel=Nat.card N45.kernel*2
    rw [N57.kernel_card,N45.kernel_card]

private def child46 (z : N46.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 66) else (if z.index.val < 3 then 59 else 58)) : Fin 68)

private theorem child46_generator_mem (z : N46.state.Row)
    (hz : N46.state.CentralInvolution generators_full z) :
    ∀ j, N46.normalGenerators j ∈ (states (child46 z)).kernel := by
  have ht := N46.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N46.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N46.normalGenerators j ∈ N66.kernel
    intro j
    have he : ∀ j : Fin 2, N46.normalGenerators j=
        (⟨N66.normalCertificate.rows (((if j.val < 1 then 5 else 9) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N66.normalCertificate _
  · change ∀ j, N46.normalGenerators j ∈ N59.kernel
    intro j
    have he : ∀ j : Fin 2, N46.normalGenerators j=
        (⟨N59.normalCertificate.rows (((if j.val < 1 then 4 else 8) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N59.normalCertificate _
  · change ∀ j, N46.normalGenerators j ∈ N58.kernel
    intro j
    have he : ∀ j : Fin 2, N46.normalGenerators j=
        (⟨N58.normalCertificate.rows (((if j.val < 1 then 4 else 8) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N58.normalCertificate _

private theorem child46_lift_mem (z : N46.state.Row)
    (hz : N46.state.CentralInvolution generators_full z) :
    N46.cosets.representatives z.index ∈ (states (child46 z)).kernel := by
  have ht := N46.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N46.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N46.cosets.representatives 1 ∈ N66.kernel
    have he : N46.cosets.representatives 1=
        (⟨N66.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N66.normalCertificate _
  · change N46.cosets.representatives 2 ∈ N59.kernel
    have he : N46.cosets.representatives 2=
        (⟨N59.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N59.normalCertificate _
  · change N46.cosets.representatives 3 ∈ N58.kernel
    have he : N46.cosets.representatives 3=
        (⟨N58.normalCertificate.rows 2⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N58.normalCertificate _

private theorem child46_card (z : N46.state.Row)
    (hz : N46.state.CentralInvolution generators_full z) :
    Nat.card (states (child46 z)).kernel=Nat.card N46.kernel*2 := by
  have ht := N46.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N46.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N66.kernel=Nat.card N46.kernel*2
    rw [N66.kernel_card,N46.kernel_card]
  · change Nat.card N59.kernel=Nat.card N46.kernel*2
    rw [N59.kernel_card,N46.kernel_card]
  · change Nat.card N58.kernel=Nat.card N46.kernel*2
    rw [N58.kernel_card,N46.kernel_card]

private def child47 (z : N47.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 65) else (if z.index.val < 3 then 58 else 60)) : Fin 68)

private theorem child47_generator_mem (z : N47.state.Row)
    (hz : N47.state.CentralInvolution generators_full z) :
    ∀ j, N47.normalGenerators j ∈ (states (child47 z)).kernel := by
  have ht := N47.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N47.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N47.normalGenerators j ∈ N65.kernel
    intro j
    have he : ∀ j : Fin 2, N47.normalGenerators j=
        (⟨N65.normalCertificate.rows (((if j.val < 1 then 5 else 8) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N65.normalCertificate _
  · change ∀ j, N47.normalGenerators j ∈ N58.kernel
    intro j
    have he : ∀ j : Fin 2, N47.normalGenerators j=
        (⟨N58.normalCertificate.rows (((if j.val < 1 then 4 else 9) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N58.normalCertificate _
  · change ∀ j, N47.normalGenerators j ∈ N60.kernel
    intro j
    have he : ∀ j : Fin 2, N47.normalGenerators j=
        (⟨N60.normalCertificate.rows (((if j.val < 1 then 4 else 9) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N60.normalCertificate _

private theorem child47_lift_mem (z : N47.state.Row)
    (hz : N47.state.CentralInvolution generators_full z) :
    N47.cosets.representatives z.index ∈ (states (child47 z)).kernel := by
  have ht := N47.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N47.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N47.cosets.representatives 1 ∈ N65.kernel
    have he : N47.cosets.representatives 1=
        (⟨N65.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N65.normalCertificate _
  · change N47.cosets.representatives 2 ∈ N58.kernel
    have he : N47.cosets.representatives 2=
        (⟨N58.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N58.normalCertificate _
  · change N47.cosets.representatives 3 ∈ N60.kernel
    have he : N47.cosets.representatives 3=
        (⟨N60.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N60.normalCertificate _

private theorem child47_card (z : N47.state.Row)
    (hz : N47.state.CentralInvolution generators_full z) :
    Nat.card (states (child47 z)).kernel=Nat.card N47.kernel*2 := by
  have ht := N47.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N47.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N65.kernel=Nat.card N47.kernel*2
    rw [N65.kernel_card,N47.kernel_card]
  · change Nat.card N58.kernel=Nat.card N47.kernel*2
    rw [N58.kernel_card,N47.kernel_card]
  · change Nat.card N60.kernel=Nat.card N47.kernel*2
    rw [N60.kernel_card,N47.kernel_card]

private def child48 (z : N48.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 61) else (if z.index.val < 3 then 63 else 57)) : Fin 68)

private theorem child48_generator_mem (z : N48.state.Row)
    (hz : N48.state.CentralInvolution generators_full z) :
    ∀ j, N48.normalGenerators j ∈ (states (child48 z)).kernel := by
  have ht := N48.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N48.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N48.normalGenerators j ∈ N61.kernel
    intro j
    have he : ∀ j : Fin 2, N48.normalGenerators j=
        (⟨N61.normalCertificate.rows (((if j.val < 1 then 5 else 9) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N61.normalCertificate _
  · change ∀ j, N48.normalGenerators j ∈ N63.kernel
    intro j
    have he : ∀ j : Fin 2, N48.normalGenerators j=
        (⟨N63.normalCertificate.rows (((if j.val < 1 then 4 else 9) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N63.normalCertificate _
  · change ∀ j, N48.normalGenerators j ∈ N57.kernel
    intro j
    have he : ∀ j : Fin 2, N48.normalGenerators j=
        (⟨N57.normalCertificate.rows (((if j.val < 1 then 5 else 9) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N57.normalCertificate _

private theorem child48_lift_mem (z : N48.state.Row)
    (hz : N48.state.CentralInvolution generators_full z) :
    N48.cosets.representatives z.index ∈ (states (child48 z)).kernel := by
  have ht := N48.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N48.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N48.cosets.representatives 1 ∈ N61.kernel
    have he : N48.cosets.representatives 1=
        (⟨N61.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N61.normalCertificate _
  · change N48.cosets.representatives 2 ∈ N63.kernel
    have he : N48.cosets.representatives 2=
        (⟨N63.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N63.normalCertificate _
  · change N48.cosets.representatives 3 ∈ N57.kernel
    have he : N48.cosets.representatives 3=
        (⟨N57.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N57.normalCertificate _

private theorem child48_card (z : N48.state.Row)
    (hz : N48.state.CentralInvolution generators_full z) :
    Nat.card (states (child48 z)).kernel=Nat.card N48.kernel*2 := by
  have ht := N48.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N48.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N61.kernel=Nat.card N48.kernel*2
    rw [N61.kernel_card,N48.kernel_card]
  · change Nat.card N63.kernel=Nat.card N48.kernel*2
    rw [N63.kernel_card,N48.kernel_card]
  · change Nat.card N57.kernel=Nat.card N48.kernel*2
    rw [N57.kernel_card,N48.kernel_card]

private def child49 (z : N49.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 62) else (if z.index.val < 3 then 64 else 57)) : Fin 68)

private theorem child49_generator_mem (z : N49.state.Row)
    (hz : N49.state.CentralInvolution generators_full z) :
    ∀ j, N49.normalGenerators j ∈ (states (child49 z)).kernel := by
  have ht := N49.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N49.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N49.normalGenerators j ∈ N62.kernel
    intro j
    have he : ∀ j : Fin 2, N49.normalGenerators j=
        (⟨N62.normalCertificate.rows (((if j.val < 1 then 5 else 8) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N62.normalCertificate _
  · change ∀ j, N49.normalGenerators j ∈ N64.kernel
    intro j
    have he : ∀ j : Fin 2, N49.normalGenerators j=
        (⟨N64.normalCertificate.rows (((if j.val < 1 then 4 else 8) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N64.normalCertificate _
  · change ∀ j, N49.normalGenerators j ∈ N57.kernel
    intro j
    have he : ∀ j : Fin 2, N49.normalGenerators j=
        (⟨N57.normalCertificate.rows (((if j.val < 1 then 5 else 8) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N57.normalCertificate _

private theorem child49_lift_mem (z : N49.state.Row)
    (hz : N49.state.CentralInvolution generators_full z) :
    N49.cosets.representatives z.index ∈ (states (child49 z)).kernel := by
  have ht := N49.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N49.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N49.cosets.representatives 1 ∈ N62.kernel
    have he : N49.cosets.representatives 1=
        (⟨N62.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N62.normalCertificate _
  · change N49.cosets.representatives 2 ∈ N64.kernel
    have he : N49.cosets.representatives 2=
        (⟨N64.normalCertificate.rows 6⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N64.normalCertificate _
  · change N49.cosets.representatives 3 ∈ N57.kernel
    have he : N49.cosets.representatives 3=
        (⟨N57.normalCertificate.rows 10⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N57.normalCertificate _

private theorem child49_card (z : N49.state.Row)
    (hz : N49.state.CentralInvolution generators_full z) :
    Nat.card (states (child49 z)).kernel=Nat.card N49.kernel*2 := by
  have ht := N49.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N49.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N62.kernel=Nat.card N49.kernel*2
    rw [N62.kernel_card,N49.kernel_card]
  · change Nat.card N64.kernel=Nat.card N49.kernel*2
    rw [N64.kernel_card,N49.kernel_card]
  · change Nat.card N57.kernel=Nat.card N49.kernel*2
    rw [N57.kernel_card,N49.kernel_card]

private def child50 (z : N50.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 61) else (if z.index.val < 3 then 64 else 58)) : Fin 68)

private theorem child50_generator_mem (z : N50.state.Row)
    (hz : N50.state.CentralInvolution generators_full z) :
    ∀ j, N50.normalGenerators j ∈ (states (child50 z)).kernel := by
  have ht := N50.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N50.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N50.normalGenerators j ∈ N61.kernel
    intro j
    have he : ∀ j : Fin 2, N50.normalGenerators j=
        (⟨N61.normalCertificate.rows (((if j.val < 1 then 5 else 8) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N61.normalCertificate _
  · change ∀ j, N50.normalGenerators j ∈ N64.kernel
    intro j
    have he : ∀ j : Fin 2, N50.normalGenerators j=
        (⟨N64.normalCertificate.rows (((if j.val < 1 then 4 else 9) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N64.normalCertificate _
  · change ∀ j, N50.normalGenerators j ∈ N58.kernel
    intro j
    have he : ∀ j : Fin 2, N50.normalGenerators j=
        (⟨N58.normalCertificate.rows (((if j.val < 1 then 5 else 8) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N58.normalCertificate _

private theorem child50_lift_mem (z : N50.state.Row)
    (hz : N50.state.CentralInvolution generators_full z) :
    N50.cosets.representatives z.index ∈ (states (child50 z)).kernel := by
  have ht := N50.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N50.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N50.cosets.representatives 1 ∈ N61.kernel
    have he : N50.cosets.representatives 1=
        (⟨N61.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N61.normalCertificate _
  · change N50.cosets.representatives 2 ∈ N64.kernel
    have he : N50.cosets.representatives 2=
        (⟨N64.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N64.normalCertificate _
  · change N50.cosets.representatives 3 ∈ N58.kernel
    have he : N50.cosets.representatives 3=
        (⟨N58.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N58.normalCertificate _

private theorem child50_card (z : N50.state.Row)
    (hz : N50.state.CentralInvolution generators_full z) :
    Nat.card (states (child50 z)).kernel=Nat.card N50.kernel*2 := by
  have ht := N50.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N50.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N61.kernel=Nat.card N50.kernel*2
    rw [N61.kernel_card,N50.kernel_card]
  · change Nat.card N64.kernel=Nat.card N50.kernel*2
    rw [N64.kernel_card,N50.kernel_card]
  · change Nat.card N58.kernel=Nat.card N50.kernel*2
    rw [N58.kernel_card,N50.kernel_card]

private def child51 (z : N51.state.Row) : Fin 68 :=
  ((if z.index.val < 2 then (if z.index.val < 1 then 0 else 62) else (if z.index.val < 3 then 58 else 63)) : Fin 68)

private theorem child51_generator_mem (z : N51.state.Row)
    (hz : N51.state.CentralInvolution generators_full z) :
    ∀ j, N51.normalGenerators j ∈ (states (child51 z)).kernel := by
  have ht := N51.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N51.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N51.normalGenerators j ∈ N62.kernel
    intro j
    have he : ∀ j : Fin 2, N51.normalGenerators j=
        (⟨N62.normalCertificate.rows (((if j.val < 1 then 5 else 9) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N62.normalCertificate _
  · change ∀ j, N51.normalGenerators j ∈ N58.kernel
    intro j
    have he : ∀ j : Fin 2, N51.normalGenerators j=
        (⟨N58.normalCertificate.rows (((if j.val < 1 then 5 else 9) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N58.normalCertificate _
  · change ∀ j, N51.normalGenerators j ∈ N63.kernel
    intro j
    have he : ∀ j : Fin 2, N51.normalGenerators j=
        (⟨N63.normalCertificate.rows (((if j.val < 1 then 4 else 8) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N63.normalCertificate _

private theorem child51_lift_mem (z : N51.state.Row)
    (hz : N51.state.CentralInvolution generators_full z) :
    N51.cosets.representatives z.index ∈ (states (child51 z)).kernel := by
  have ht := N51.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N51.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N51.cosets.representatives 1 ∈ N62.kernel
    have he : N51.cosets.representatives 1=
        (⟨N62.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N62.normalCertificate _
  · change N51.cosets.representatives 2 ∈ N58.kernel
    have he : N51.cosets.representatives 2=
        (⟨N58.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N58.normalCertificate _
  · change N51.cosets.representatives 3 ∈ N63.kernel
    have he : N51.cosets.representatives 3=
        (⟨N63.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N63.normalCertificate _

private theorem child51_card (z : N51.state.Row)
    (hz : N51.state.CentralInvolution generators_full z) :
    Nat.card (states (child51 z)).kernel=Nat.card N51.kernel*2 := by
  have ht := N51.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N51.state.centralRowTests generators_full ⟨(0 : Fin 4)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N62.kernel=Nat.card N51.kernel*2
    rw [N62.kernel_card,N51.kernel_card]
  · change Nat.card N58.kernel=Nat.card N51.kernel*2
    rw [N58.kernel_card,N51.kernel_card]
  · change Nat.card N63.kernel=Nat.card N51.kernel*2
    rw [N63.kernel_card,N51.kernel_card]

private def child52 (z : N52.state.Row) : Fin 68 :=
  ((if z.index.val < 1 then 0 else 67) : Fin 68)

private theorem child52_generator_mem (z : N52.state.Row)
    (hz : N52.state.CentralInvolution generators_full z) :
    ∀ j, N52.normalGenerators j ∈ (states (child52 z)).kernel := by
  have ht := N52.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N52.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N52.normalGenerators j ∈ N67.kernel
    intro j
    have he : ∀ j : Fin 3, N52.normalGenerators j=
        (⟨N67.normalCertificate.rows (((if j.val < 1 then 28 else (if j.val < 2 then 29 else 11)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N67.normalCertificate _

private theorem child52_lift_mem (z : N52.state.Row)
    (hz : N52.state.CentralInvolution generators_full z) :
    N52.cosets.representatives z.index ∈ (states (child52 z)).kernel := by
  have ht := N52.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N52.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N52.cosets.representatives 1 ∈ N67.kernel
    have he : N52.cosets.representatives 1=
        (⟨N67.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N67.normalCertificate _

private theorem child52_card (z : N52.state.Row)
    (hz : N52.state.CentralInvolution generators_full z) :
    Nat.card (states (child52 z)).kernel=Nat.card N52.kernel*2 := by
  have ht := N52.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N52.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N67.kernel=Nat.card N52.kernel*2
    rw [N67.kernel_card,N52.kernel_card]

private def child53 (z : N53.state.Row) : Fin 68 :=
  ((if z.index.val < 1 then 0 else 67) : Fin 68)

private theorem child53_generator_mem (z : N53.state.Row)
    (hz : N53.state.CentralInvolution generators_full z) :
    ∀ j, N53.normalGenerators j ∈ (states (child53 z)).kernel := by
  have ht := N53.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N53.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N53.normalGenerators j ∈ N67.kernel
    intro j
    have he : ∀ j : Fin 3, N53.normalGenerators j=
        (⟨N67.normalCertificate.rows (((if j.val < 1 then 28 else (if j.val < 2 then 29 else 19)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N67.normalCertificate _

private theorem child53_lift_mem (z : N53.state.Row)
    (hz : N53.state.CentralInvolution generators_full z) :
    N53.cosets.representatives z.index ∈ (states (child53 z)).kernel := by
  have ht := N53.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N53.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N53.cosets.representatives 1 ∈ N67.kernel
    have he : N53.cosets.representatives 1=
        (⟨N67.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N67.normalCertificate _

private theorem child53_card (z : N53.state.Row)
    (hz : N53.state.CentralInvolution generators_full z) :
    Nat.card (states (child53 z)).kernel=Nat.card N53.kernel*2 := by
  have ht := N53.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N53.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N67.kernel=Nat.card N53.kernel*2
    rw [N67.kernel_card,N53.kernel_card]

private def child54 (z : N54.state.Row) : Fin 68 :=
  ((if z.index.val < 1 then 0 else 67) : Fin 68)

private theorem child54_generator_mem (z : N54.state.Row)
    (hz : N54.state.CentralInvolution generators_full z) :
    ∀ j, N54.normalGenerators j ∈ (states (child54 z)).kernel := by
  have ht := N54.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N54.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N54.normalGenerators j ∈ N67.kernel
    intro j
    have he : ∀ j : Fin 3, N54.normalGenerators j=
        (⟨N67.normalCertificate.rows (((if j.val < 1 then 28 else (if j.val < 2 then 29 else 27)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N67.normalCertificate _

private theorem child54_lift_mem (z : N54.state.Row)
    (hz : N54.state.CentralInvolution generators_full z) :
    N54.cosets.representatives z.index ∈ (states (child54 z)).kernel := by
  have ht := N54.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N54.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N54.cosets.representatives 1 ∈ N67.kernel
    have he : N54.cosets.representatives 1=
        (⟨N67.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N67.normalCertificate _

private theorem child54_card (z : N54.state.Row)
    (hz : N54.state.CentralInvolution generators_full z) :
    Nat.card (states (child54 z)).kernel=Nat.card N54.kernel*2 := by
  have ht := N54.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N54.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N67.kernel=Nat.card N54.kernel*2
    rw [N67.kernel_card,N54.kernel_card]

private def child55 (z : N55.state.Row) : Fin 68 :=
  ((if z.index.val < 1 then 0 else 67) : Fin 68)

private theorem child55_generator_mem (z : N55.state.Row)
    (hz : N55.state.CentralInvolution generators_full z) :
    ∀ j, N55.normalGenerators j ∈ (states (child55 z)).kernel := by
  have ht := N55.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N55.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N55.normalGenerators j ∈ N67.kernel
    intro j
    have he : ∀ j : Fin 4, N55.normalGenerators j=
        (⟨N67.normalCertificate.rows (((if j.val < 2 then (if j.val < 1 then 28 else 11) else (if j.val < 3 then 7 else 19)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N67.normalCertificate _

private theorem child55_lift_mem (z : N55.state.Row)
    (hz : N55.state.CentralInvolution generators_full z) :
    N55.cosets.representatives z.index ∈ (states (child55 z)).kernel := by
  have ht := N55.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N55.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N55.cosets.representatives 1 ∈ N67.kernel
    have he : N55.cosets.representatives 1=
        (⟨N67.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N67.normalCertificate _

private theorem child55_card (z : N55.state.Row)
    (hz : N55.state.CentralInvolution generators_full z) :
    Nat.card (states (child55 z)).kernel=Nat.card N55.kernel*2 := by
  have ht := N55.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N55.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N67.kernel=Nat.card N55.kernel*2
    rw [N67.kernel_card,N55.kernel_card]

private def child56 (z : N56.state.Row) : Fin 68 :=
  ((if z.index.val < 1 then 0 else 67) : Fin 68)

private theorem child56_generator_mem (z : N56.state.Row)
    (hz : N56.state.CentralInvolution generators_full z) :
    ∀ j, N56.normalGenerators j ∈ (states (child56 z)).kernel := by
  have ht := N56.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N56.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N56.normalGenerators j ∈ N67.kernel
    intro j
    have he : ∀ j : Fin 4, N56.normalGenerators j=
        (⟨N67.normalCertificate.rows (((if j.val < 2 then (if j.val < 1 then 28 else 11) else (if j.val < 3 then 7 else 17)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N67.normalCertificate _

private theorem child56_lift_mem (z : N56.state.Row)
    (hz : N56.state.CentralInvolution generators_full z) :
    N56.cosets.representatives z.index ∈ (states (child56 z)).kernel := by
  have ht := N56.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N56.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N56.cosets.representatives 1 ∈ N67.kernel
    have he : N56.cosets.representatives 1=
        (⟨N67.normalCertificate.rows 30⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N67.normalCertificate _

private theorem child56_card (z : N56.state.Row)
    (hz : N56.state.CentralInvolution generators_full z) :
    Nat.card (states (child56 z)).kernel=Nat.card N56.kernel*2 := by
  have ht := N56.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N56.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N67.kernel=Nat.card N56.kernel*2
    rw [N67.kernel_card,N56.kernel_card]

private def child57 (z : N57.state.Row) : Fin 68 :=
  ((if z.index.val < 1 then 0 else 67) : Fin 68)

private theorem child57_generator_mem (z : N57.state.Row)
    (hz : N57.state.CentralInvolution generators_full z) :
    ∀ j, N57.normalGenerators j ∈ (states (child57 z)).kernel := by
  have ht := N57.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N57.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N57.normalGenerators j ∈ N67.kernel
    intro j
    have he : ∀ j : Fin 3, N57.normalGenerators j=
        (⟨N67.normalCertificate.rows (((if j.val < 1 then 28 else (if j.val < 2 then 9 else 19)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N67.normalCertificate _

private theorem child57_lift_mem (z : N57.state.Row)
    (hz : N57.state.CentralInvolution generators_full z) :
    N57.cosets.representatives z.index ∈ (states (child57 z)).kernel := by
  have ht := N57.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N57.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N57.cosets.representatives 1 ∈ N67.kernel
    have he : N57.cosets.representatives 1=
        (⟨N67.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N67.normalCertificate _

private theorem child57_card (z : N57.state.Row)
    (hz : N57.state.CentralInvolution generators_full z) :
    Nat.card (states (child57 z)).kernel=Nat.card N57.kernel*2 := by
  have ht := N57.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N57.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N67.kernel=Nat.card N57.kernel*2
    rw [N67.kernel_card,N57.kernel_card]

private def child58 (z : N58.state.Row) : Fin 68 :=
  ((if z.index.val < 1 then 0 else 67) : Fin 68)

private theorem child58_generator_mem (z : N58.state.Row)
    (hz : N58.state.CentralInvolution generators_full z) :
    ∀ j, N58.normalGenerators j ∈ (states (child58 z)).kernel := by
  have ht := N58.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N58.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N58.normalGenerators j ∈ N67.kernel
    intro j
    have he : ∀ j : Fin 3, N58.normalGenerators j=
        (⟨N67.normalCertificate.rows (((if j.val < 1 then 28 else (if j.val < 2 then 9 else 17)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N67.normalCertificate _

private theorem child58_lift_mem (z : N58.state.Row)
    (hz : N58.state.CentralInvolution generators_full z) :
    N58.cosets.representatives z.index ∈ (states (child58 z)).kernel := by
  have ht := N58.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N58.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N58.cosets.representatives 1 ∈ N67.kernel
    have he : N58.cosets.representatives 1=
        (⟨N67.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N67.normalCertificate _

private theorem child58_card (z : N58.state.Row)
    (hz : N58.state.CentralInvolution generators_full z) :
    Nat.card (states (child58 z)).kernel=Nat.card N58.kernel*2 := by
  have ht := N58.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N58.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N67.kernel=Nat.card N58.kernel*2
    rw [N67.kernel_card,N58.kernel_card]

private def child59 (z : N59.state.Row) : Fin 68 :=
  ((if z.index.val < 1 then 0 else 67) : Fin 68)

private theorem child59_generator_mem (z : N59.state.Row)
    (hz : N59.state.CentralInvolution generators_full z) :
    ∀ j, N59.normalGenerators j ∈ (states (child59 z)).kernel := by
  have ht := N59.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N59.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N59.normalGenerators j ∈ N67.kernel
    intro j
    have he : ∀ j : Fin 3, N59.normalGenerators j=
        (⟨N67.normalCertificate.rows (((if j.val < 1 then 29 else (if j.val < 2 then 11 else 19)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N67.normalCertificate _

private theorem child59_lift_mem (z : N59.state.Row)
    (hz : N59.state.CentralInvolution generators_full z) :
    N59.cosets.representatives z.index ∈ (states (child59 z)).kernel := by
  have ht := N59.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N59.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N59.cosets.representatives 1 ∈ N67.kernel
    have he : N59.cosets.representatives 1=
        (⟨N67.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N67.normalCertificate _

private theorem child59_card (z : N59.state.Row)
    (hz : N59.state.CentralInvolution generators_full z) :
    Nat.card (states (child59 z)).kernel=Nat.card N59.kernel*2 := by
  have ht := N59.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N59.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N67.kernel=Nat.card N59.kernel*2
    rw [N67.kernel_card,N59.kernel_card]

private def child60 (z : N60.state.Row) : Fin 68 :=
  ((if z.index.val < 1 then 0 else 67) : Fin 68)

private theorem child60_generator_mem (z : N60.state.Row)
    (hz : N60.state.CentralInvolution generators_full z) :
    ∀ j, N60.normalGenerators j ∈ (states (child60 z)).kernel := by
  have ht := N60.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N60.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N60.normalGenerators j ∈ N67.kernel
    intro j
    have he : ∀ j : Fin 3, N60.normalGenerators j=
        (⟨N67.normalCertificate.rows (((if j.val < 1 then 29 else (if j.val < 2 then 11 else 16)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N67.normalCertificate _

private theorem child60_lift_mem (z : N60.state.Row)
    (hz : N60.state.CentralInvolution generators_full z) :
    N60.cosets.representatives z.index ∈ (states (child60 z)).kernel := by
  have ht := N60.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N60.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N60.cosets.representatives 1 ∈ N67.kernel
    have he : N60.cosets.representatives 1=
        (⟨N67.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N67.normalCertificate _

private theorem child60_card (z : N60.state.Row)
    (hz : N60.state.CentralInvolution generators_full z) :
    Nat.card (states (child60 z)).kernel=Nat.card N60.kernel*2 := by
  have ht := N60.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N60.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N67.kernel=Nat.card N60.kernel*2
    rw [N67.kernel_card,N60.kernel_card]

private def child61 (z : N61.state.Row) : Fin 68 :=
  ((if z.index.val < 1 then 0 else 67) : Fin 68)

private theorem child61_generator_mem (z : N61.state.Row)
    (hz : N61.state.CentralInvolution generators_full z) :
    ∀ j, N61.normalGenerators j ∈ (states (child61 z)).kernel := by
  have ht := N61.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N61.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N61.normalGenerators j ∈ N67.kernel
    intro j
    have he : ∀ j : Fin 3, N61.normalGenerators j=
        (⟨N67.normalCertificate.rows (((if j.val < 1 then 29 else (if j.val < 2 then 8 else 19)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N67.normalCertificate _

private theorem child61_lift_mem (z : N61.state.Row)
    (hz : N61.state.CentralInvolution generators_full z) :
    N61.cosets.representatives z.index ∈ (states (child61 z)).kernel := by
  have ht := N61.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N61.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N61.cosets.representatives 1 ∈ N67.kernel
    have he : N61.cosets.representatives 1=
        (⟨N67.normalCertificate.rows 30⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N67.normalCertificate _

private theorem child61_card (z : N61.state.Row)
    (hz : N61.state.CentralInvolution generators_full z) :
    Nat.card (states (child61 z)).kernel=Nat.card N61.kernel*2 := by
  have ht := N61.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N61.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N67.kernel=Nat.card N61.kernel*2
    rw [N67.kernel_card,N61.kernel_card]

private def child62 (z : N62.state.Row) : Fin 68 :=
  ((if z.index.val < 1 then 0 else 67) : Fin 68)

private theorem child62_generator_mem (z : N62.state.Row)
    (hz : N62.state.CentralInvolution generators_full z) :
    ∀ j, N62.normalGenerators j ∈ (states (child62 z)).kernel := by
  have ht := N62.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N62.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N62.normalGenerators j ∈ N67.kernel
    intro j
    have he : ∀ j : Fin 3, N62.normalGenerators j=
        (⟨N67.normalCertificate.rows (((if j.val < 1 then 29 else (if j.val < 2 then 8 else 16)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N67.normalCertificate _

private theorem child62_lift_mem (z : N62.state.Row)
    (hz : N62.state.CentralInvolution generators_full z) :
    N62.cosets.representatives z.index ∈ (states (child62 z)).kernel := by
  have ht := N62.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N62.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N62.cosets.representatives 1 ∈ N67.kernel
    have he : N62.cosets.representatives 1=
        (⟨N67.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N67.normalCertificate _

private theorem child62_card (z : N62.state.Row)
    (hz : N62.state.CentralInvolution generators_full z) :
    Nat.card (states (child62 z)).kernel=Nat.card N62.kernel*2 := by
  have ht := N62.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N62.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N67.kernel=Nat.card N62.kernel*2
    rw [N67.kernel_card,N62.kernel_card]

private def child63 (z : N63.state.Row) : Fin 68 :=
  ((if z.index.val < 1 then 0 else 67) : Fin 68)

private theorem child63_generator_mem (z : N63.state.Row)
    (hz : N63.state.CentralInvolution generators_full z) :
    ∀ j, N63.normalGenerators j ∈ (states (child63 z)).kernel := by
  have ht := N63.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N63.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N63.normalGenerators j ∈ N67.kernel
    intro j
    have he : ∀ j : Fin 3, N63.normalGenerators j=
        (⟨N67.normalCertificate.rows (((if j.val < 1 then 30 else (if j.val < 2 then 11 else 19)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N67.normalCertificate _

private theorem child63_lift_mem (z : N63.state.Row)
    (hz : N63.state.CentralInvolution generators_full z) :
    N63.cosets.representatives z.index ∈ (states (child63 z)).kernel := by
  have ht := N63.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N63.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N63.cosets.representatives 1 ∈ N67.kernel
    have he : N63.cosets.representatives 1=
        (⟨N67.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N67.normalCertificate _

private theorem child63_card (z : N63.state.Row)
    (hz : N63.state.CentralInvolution generators_full z) :
    Nat.card (states (child63 z)).kernel=Nat.card N63.kernel*2 := by
  have ht := N63.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N63.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N67.kernel=Nat.card N63.kernel*2
    rw [N67.kernel_card,N63.kernel_card]

private def child64 (z : N64.state.Row) : Fin 68 :=
  ((if z.index.val < 1 then 0 else 67) : Fin 68)

private theorem child64_generator_mem (z : N64.state.Row)
    (hz : N64.state.CentralInvolution generators_full z) :
    ∀ j, N64.normalGenerators j ∈ (states (child64 z)).kernel := by
  have ht := N64.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N64.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N64.normalGenerators j ∈ N67.kernel
    intro j
    have he : ∀ j : Fin 3, N64.normalGenerators j=
        (⟨N67.normalCertificate.rows (((if j.val < 1 then 30 else (if j.val < 2 then 11 else 16)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N67.normalCertificate _

private theorem child64_lift_mem (z : N64.state.Row)
    (hz : N64.state.CentralInvolution generators_full z) :
    N64.cosets.representatives z.index ∈ (states (child64 z)).kernel := by
  have ht := N64.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N64.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N64.cosets.representatives 1 ∈ N67.kernel
    have he : N64.cosets.representatives 1=
        (⟨N67.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N67.normalCertificate _

private theorem child64_card (z : N64.state.Row)
    (hz : N64.state.CentralInvolution generators_full z) :
    Nat.card (states (child64 z)).kernel=Nat.card N64.kernel*2 := by
  have ht := N64.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N64.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N67.kernel=Nat.card N64.kernel*2
    rw [N67.kernel_card,N64.kernel_card]

private def child65 (z : N65.state.Row) : Fin 68 :=
  ((if z.index.val < 1 then 0 else 67) : Fin 68)

private theorem child65_generator_mem (z : N65.state.Row)
    (hz : N65.state.CentralInvolution generators_full z) :
    ∀ j, N65.normalGenerators j ∈ (states (child65 z)).kernel := by
  have ht := N65.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N65.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N65.normalGenerators j ∈ N67.kernel
    intro j
    have he : ∀ j : Fin 3, N65.normalGenerators j=
        (⟨N67.normalCertificate.rows (((if j.val < 1 then 30 else (if j.val < 2 then 8 else 19)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N67.normalCertificate _

private theorem child65_lift_mem (z : N65.state.Row)
    (hz : N65.state.CentralInvolution generators_full z) :
    N65.cosets.representatives z.index ∈ (states (child65 z)).kernel := by
  have ht := N65.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N65.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N65.cosets.representatives 1 ∈ N67.kernel
    have he : N65.cosets.representatives 1=
        (⟨N67.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N67.normalCertificate _

private theorem child65_card (z : N65.state.Row)
    (hz : N65.state.CentralInvolution generators_full z) :
    Nat.card (states (child65 z)).kernel=Nat.card N65.kernel*2 := by
  have ht := N65.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N65.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N67.kernel=Nat.card N65.kernel*2
    rw [N67.kernel_card,N65.kernel_card]

private def child66 (z : N66.state.Row) : Fin 68 :=
  ((if z.index.val < 1 then 0 else 67) : Fin 68)

private theorem child66_generator_mem (z : N66.state.Row)
    (hz : N66.state.CentralInvolution generators_full z) :
    ∀ j, N66.normalGenerators j ∈ (states (child66 z)).kernel := by
  have ht := N66.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N66.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change ∀ j, N66.normalGenerators j ∈ N67.kernel
    intro j
    have he : ∀ j : Fin 3, N66.normalGenerators j=
        (⟨N67.normalCertificate.rows (((if j.val < 1 then 30 else (if j.val < 2 then 8 else 16)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N67.normalCertificate _

private theorem child66_lift_mem (z : N66.state.Row)
    (hz : N66.state.CentralInvolution generators_full z) :
    N66.cosets.representatives z.index ∈ (states (child66 z)).kernel := by
  have ht := N66.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N66.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change N66.cosets.representatives 1 ∈ N67.kernel
    have he : N66.cosets.representatives 1=
        (⟨N67.normalCertificate.rows 29⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N67.normalCertificate _

private theorem child66_card (z : N66.state.Row)
    (hz : N66.state.CentralInvolution generators_full z) :
    Nat.card (states (child66 z)).kernel=Nat.card N66.kernel*2 := by
  have ht := N66.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N66.state.centralRowTests generators_full ⟨(0 : Fin 2)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)
  · change Nat.card N67.kernel=Nat.card N66.kernel*2
    rw [N67.kernel_card,N66.kernel_card]

private def child67 (z : N67.state.Row) : Fin 68 :=
  (0 : Fin 68)

private theorem child67_generator_mem (z : N67.state.Row)
    (hz : N67.state.CentralInvolution generators_full z) :
    ∀ j, N67.normalGenerators j ∈ (states (child67 z)).kernel := by
  have ht := N67.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N67.state.centralRowTests generators_full ⟨(0 : Fin 1)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)

private theorem child67_lift_mem (z : N67.state.Row)
    (hz : N67.state.CentralInvolution generators_full z) :
    N67.cosets.representatives z.index ∈ (states (child67 z)).kernel := by
  have ht := N67.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N67.state.centralRowTests generators_full ⟨(0 : Fin 1)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)

private theorem child67_card (z : N67.state.Row)
    (hz : N67.state.CentralInvolution generators_full z) :
    Nat.card (states (child67 z)).kernel=Nat.card N67.kernel*2 := by
  have ht := N67.state.centralInvolution_rowTests generators_full z hz
  rcases z with ⟨z⟩
  fin_cases z
  · have hf : ¬N67.state.centralRowTests generators_full ⟨(0 : Fin 1)⟩ := by unfold BinaryNormalState.centralRowTests; decide +kernel
    exact False.elim (hf ht)

private def child : (i : Fin 68) → (states i).Row → Fin 68 :=
  (Fin.cases child0 (Fin.cases child1 (Fin.cases child2 (Fin.cases child3 (Fin.cases child4 (Fin.cases child5 (Fin.cases child6 (Fin.cases child7 (Fin.cases child8 (Fin.cases child9 (Fin.cases child10 (Fin.cases child11 (Fin.cases child12 (Fin.cases child13 (Fin.cases child14 (Fin.cases child15 (Fin.cases child16 (Fin.cases child17 (Fin.cases child18 (Fin.cases child19 (Fin.cases child20 (Fin.cases child21 (Fin.cases child22 (Fin.cases child23 (Fin.cases child24 (Fin.cases child25 (Fin.cases child26 (Fin.cases child27 (Fin.cases child28 (Fin.cases child29 (Fin.cases child30 (Fin.cases child31 (Fin.cases child32 (Fin.cases child33 (Fin.cases child34 (Fin.cases child35 (Fin.cases child36 (Fin.cases child37 (Fin.cases child38 (Fin.cases child39 (Fin.cases child40 (Fin.cases child41 (Fin.cases child42 (Fin.cases child43 (Fin.cases child44 (Fin.cases child45 (Fin.cases child46 (Fin.cases child47 (Fin.cases child48 (Fin.cases child49 (Fin.cases child50 (Fin.cases child51 (Fin.cases child52 (Fin.cases child53 (Fin.cases child54 (Fin.cases child55 (Fin.cases child56 (Fin.cases child57 (Fin.cases child58 (Fin.cases child59 (Fin.cases child60 (Fin.cases child61 (Fin.cases child62 (Fin.cases child63 (Fin.cases child64 (Fin.cases child65 (Fin.cases child66 (Fin.cases child67 (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

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
    · exact child20_generator_mem
    · exact child21_generator_mem
    · exact child22_generator_mem
    · exact child23_generator_mem
    · exact child24_generator_mem
    · exact child25_generator_mem
    · exact child26_generator_mem
    · exact child27_generator_mem
    · exact child28_generator_mem
    · exact child29_generator_mem
    · exact child30_generator_mem
    · exact child31_generator_mem
    · exact child32_generator_mem
    · exact child33_generator_mem
    · exact child34_generator_mem
    · exact child35_generator_mem
    · exact child36_generator_mem
    · exact child37_generator_mem
    · exact child38_generator_mem
    · exact child39_generator_mem
    · exact child40_generator_mem
    · exact child41_generator_mem
    · exact child42_generator_mem
    · exact child43_generator_mem
    · exact child44_generator_mem
    · exact child45_generator_mem
    · exact child46_generator_mem
    · exact child47_generator_mem
    · exact child48_generator_mem
    · exact child49_generator_mem
    · exact child50_generator_mem
    · exact child51_generator_mem
    · exact child52_generator_mem
    · exact child53_generator_mem
    · exact child54_generator_mem
    · exact child55_generator_mem
    · exact child56_generator_mem
    · exact child57_generator_mem
    · exact child58_generator_mem
    · exact child59_generator_mem
    · exact child60_generator_mem
    · exact child61_generator_mem
    · exact child62_generator_mem
    · exact child63_generator_mem
    · exact child64_generator_mem
    · exact child65_generator_mem
    · exact child66_generator_mem
    · exact child67_generator_mem
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
    · exact child20_lift_mem
    · exact child21_lift_mem
    · exact child22_lift_mem
    · exact child23_lift_mem
    · exact child24_lift_mem
    · exact child25_lift_mem
    · exact child26_lift_mem
    · exact child27_lift_mem
    · exact child28_lift_mem
    · exact child29_lift_mem
    · exact child30_lift_mem
    · exact child31_lift_mem
    · exact child32_lift_mem
    · exact child33_lift_mem
    · exact child34_lift_mem
    · exact child35_lift_mem
    · exact child36_lift_mem
    · exact child37_lift_mem
    · exact child38_lift_mem
    · exact child39_lift_mem
    · exact child40_lift_mem
    · exact child41_lift_mem
    · exact child42_lift_mem
    · exact child43_lift_mem
    · exact child44_lift_mem
    · exact child45_lift_mem
    · exact child46_lift_mem
    · exact child47_lift_mem
    · exact child48_lift_mem
    · exact child49_lift_mem
    · exact child50_lift_mem
    · exact child51_lift_mem
    · exact child52_lift_mem
    · exact child53_lift_mem
    · exact child54_lift_mem
    · exact child55_lift_mem
    · exact child56_lift_mem
    · exact child57_lift_mem
    · exact child58_lift_mem
    · exact child59_lift_mem
    · exact child60_lift_mem
    · exact child61_lift_mem
    · exact child62_lift_mem
    · exact child63_lift_mem
    · exact child64_lift_mem
    · exact child65_lift_mem
    · exact child66_lift_mem
    · exact child67_lift_mem
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
    · exact child20_card
    · exact child21_card
    · exact child22_card
    · exact child23_card
    · exact child24_card
    · exact child25_card
    · exact child26_card
    · exact child27_card
    · exact child28_card
    · exact child29_card
    · exact child30_card
    · exact child31_card
    · exact child32_card
    · exact child33_card
    · exact child34_card
    · exact child35_card
    · exact child36_card
    · exact child37_card
    · exact child38_card
    · exact child39_card
    · exact child40_card
    · exact child41_card
    · exact child42_card
    · exact child43_card
    · exact child44_card
    · exact child45_card
    · exact child46_card
    · exact child47_card
    · exact child48_card
    · exact child49_card
    · exact child50_card
    · exact child51_card
    · exact child52_card
    · exact child53_card
    · exact child54_card
    · exact child55_card
    · exact child56_card
    · exact child57_card
    · exact child58_card
    · exact child59_card
    · exact child60_card
    · exact child61_card
    · exact child62_card
    · exact child63_card
    · exact child64_card
    · exact child65_card
    · exact child66_card
    · exact child67_card

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

end SymmetricSubgroupAsymptotics.BinaryNormal8T22
