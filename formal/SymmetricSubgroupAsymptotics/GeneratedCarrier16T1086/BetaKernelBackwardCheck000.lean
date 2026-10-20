import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaMapsData

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

theorem betaKernelBackwardChecked000 : ∀ i : Fin 1,
    (0 : ℕ) ≤ i.val → i.val < 1 → betaSource (betaKernelBackward i) = coverKernelElement i ∧ betaTarget (betaKernelBackward i) = 1 := by decide +kernel


end SymmetricSubgroupAsymptotics.BinaryChart16T1086
